use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};

use rayon::iter::{IntoParallelIterator, ParallelIterator};

#[derive(Debug, Clone)]
// is only a single node in the recursion tree, does not in general (except the root node) represent the original problem
struct ProblemState {
    clauses: BTreeMap<u64, BTreeSet<i64>>, // indexed by u64, is a collection of literal names i64s
    literals: BTreeMap<i64, BTreeSet<u64>>, // named by i64, is a collection of indexes into 'clauses'

    clause_counter: u64, // for the dynamic adding of clauses; only increases; dead indices stay dead

    trails: [Vec<(i64, u64)>; 3], // trails of forced assignments (pure, unit) or decisions (heuristic) along a rollout in the recursive search tree

    depth: u64,
}

impl ProblemState {
    // dynamic insertion of clauses; not meaningful if cdcl is not implemented
    fn insert_clause(&mut self, clause: BTreeSet<i64>) {
        for var in &clause {
            self.literals
                .get_mut(var)
                .unwrap()
                .insert(self.clause_counter);
        }
        self.clauses.insert(self.clause_counter, clause);
        self.clause_counter += 1;
    }
}

// reading a dimac .cnf file into a root node
fn read_cnf(file_path: &str) -> ProblemState {
    let contents = fs::read_to_string(file_path).expect("Couldn't read from file_path {file_path}");
    let contents = contents.split("cnf").collect::<Vec<&str>>();
    let contents = *contents.last().unwrap();
    let contents = contents.split_whitespace().collect::<Vec<&str>>();
    let mut contents = contents
        .into_iter()
        .filter_map(|x| x.parse().ok())
        .collect::<Vec<i64>>();

    let (num_vars, num_clauses) = (contents[0], contents[1]);
    let _ = contents.remove(0) & contents.remove(0);

    let mut problem: ProblemState = ProblemState {
        clauses: BTreeMap::new(),
        literals: BTreeMap::from_iter(
            (-num_vars..=num_vars)
                .into_iter()
                .filter(|x| x != &0)
                .map(|i| (i, BTreeSet::new())),
        ),
        clause_counter: 0,

        trails: [vec![], vec![], vec![]],

        depth: 0,
    };

    let mut clause = BTreeSet::new();
    for x in contents.iter_mut() {
        if x != &0 {
            clause.insert(x.clone());
        } else {
            if clause.len() > 0 {
                problem.insert_clause(clause.clone());
            }
            clause.clear();
        }
    }

    assert_eq!(
        problem.clauses.len(),
        num_clauses as usize,
        "Found {} clauses, expected {num_clauses} clauses.",
        problem.clauses.len()
    );
    return problem;
}

// sanity, checks the trail if sat, if DPLL claims sat
fn verify_trail(problem_state: ProblemState, trails: [Vec<(i64, u64)>; 3]) -> bool {
    let assignments: BTreeSet<i64> = BTreeSet::from_iter(
        [trails[1].clone(), trails[2].clone()]
            .concat()
            .into_iter()
            .map(|x| x.0)
            .collect::<Vec<i64>>(),
    );

    'outer: for (_, clause) in problem_state.clauses {
        for literal in &clause {
            if assignments.contains(literal) {
                // println!("[{:?}:  {:?}]", clause, literal);
                continue 'outer;
            }
        }

        println!(
            "conflict at clause {:?} with assignments {:?}",
            clause, assignments
        );
        return false;
    }
    return true;
}

// returns the first unit clause's literal, 0 if none
fn find_unit(problem_state: &ProblemState) -> i64 {
    for (_, c) in problem_state.clauses.iter() {
        if c.len() == 1 {
            return *c.iter().next().unwrap();
        }
    }
    return 0;
}

// propagates a found unit literal; does not check for correctness but assumes unit, likely malfunctions if asked to propagate non-unit
fn unit_propagate(l: i64, mut problem_state: ProblemState) -> ProblemState {
    for cidx in problem_state.literals.get_mut(&l).cloned().unwrap() {
        let removed_clause = problem_state.clauses.remove(&cidx).unwrap();
        for literal in removed_clause {
            problem_state
                .literals
                .get_mut(&literal)
                .unwrap()
                .remove(&cidx);
        }
    }
    for cidx in problem_state.literals.get_mut(&-l).cloned().unwrap() {
        problem_state.clauses.get_mut(&cidx).unwrap().remove(&-l);
    }

    problem_state.literals.remove(&l);
    problem_state.literals.remove(&-l);

    problem_state.trails[1].push((l, problem_state.depth));
    problem_state.depth += 1;

    return problem_state;
}

fn find_pure(problem_state: &ProblemState) -> i64 {
    // returns the first pure literal, 0 if none
    for l in problem_state.literals.keys() {
        if problem_state.literals.get(&-l).unwrap().is_empty() {
            return *l;
        }
    }
    return 0;
}

// propagates a found pure literal; likely malfunctions in the same mode as unit_propagate
fn pure_propagate(l: i64, mut problem_state: ProblemState) -> ProblemState {
    for lc in [l, -l] {
        {
            for cidx in problem_state.literals.get_mut(&lc).cloned().unwrap() {
                let removed_clause = problem_state.clauses.remove(&cidx).unwrap();
                for literal in removed_clause {
                    problem_state
                        .literals
                        .get_mut(&literal)
                        .unwrap()
                        .remove(&cidx);
                }
            }
            problem_state.literals.remove(&lc);
        }
    }

    problem_state.trails[2].push((l, problem_state.depth));
    problem_state.depth += 1;

    return problem_state;
}

// baseline literal decision, returns the next literal in the BTreeSet's (deterministic but arbitrary) iterator
fn next_literal(problem_state: ProblemState) -> (ProblemState, i64) {
    let literal = &problem_state.literals.keys().next().unwrap().clone();
    (problem_state, *literal)
}

// literal that occurs in the most clauses
fn maximum_occurence(problem_state: ProblemState) -> (ProblemState, i64) {
    let (mut max, mut max_literal) = (0, 0);

    for literal in problem_state.literals.keys() {
        let literal_clause_count = problem_state.literals.get(literal).iter().len();
        if literal_clause_count > max {
            (max, max_literal) = (literal_clause_count, *literal);
        }
    }
    (problem_state, max_literal)
}

// maximum occurence of minimum size
fn moms(problem_state: ProblemState) -> (ProblemState, i64) {
    let mut min_length = *&problem_state.clauses.iter().next().unwrap().1.len();
    let mut smallest_clauses: Vec<u64> = vec![];

    for clause in &problem_state.clauses {
        let clause_len = clause.1.len();
        if clause_len <= min_length {
            if clause_len < min_length {
                smallest_clauses.clear();
                min_length = clause_len;
            }
            smallest_clauses.push(*clause.0);
        }
    }

    let mut literal_counts: BTreeMap<i64, u64> = BTreeMap::new();
    for cindex in smallest_clauses {
        for literal in problem_state.clauses.get(&cindex).unwrap() {
            if !literal_counts.contains_key(literal) {
                literal_counts.insert(*literal, 0);
            }
            *literal_counts.get_mut(literal).unwrap() += 1;
        }
    }

    let (mut max_literal, mut max) = (0, 0);

    for (literal, count) in literal_counts {
        if count > max {
            (max_literal, max) = (literal, count)
        }
    }

    (problem_state, max_literal)
}

const DEPTH_LIMIT: u64 = 0;

struct DPLL {
    nodes: Arc<Mutex<u64>>,
    max_depth: Arc<Mutex<u64>>,

    heuristic: fn(ProblemState) -> (ProblemState, i64),
}

impl DPLL {
    fn dpll(&self, mut problem_state: ProblemState) -> (bool, ProblemState) {
        if DEPTH_LIMIT != 0 {
            if problem_state.depth > DEPTH_LIMIT {
                return (false, problem_state);
            }
        }

        *self.nodes.lock().unwrap() += 1;

        print!(
            "\rNodes explored: {}, Max depth reached: {} ",
            *self.nodes.lock().unwrap(),
            *self.max_depth.lock().unwrap()
        );

        problem_state.depth += 1;
        if problem_state.depth > *self.max_depth.lock().unwrap() {
            *self.max_depth.lock().unwrap() = problem_state.depth;
        }

        loop {
            let unit = find_unit(&problem_state);
            if unit == 0 {
                break;
            }

            problem_state = unit_propagate(unit, problem_state);
        }

        loop {
            let pure = find_pure(&problem_state);
            if pure == 0 {
                break;
            }

            problem_state = pure_propagate(pure, problem_state);
        }

        if problem_state.clauses.is_empty() {
            // println!("{:?}", (problem.decision_trail, problem.unit_trail, problem.pure_trail));
            return (true, problem_state);
        }
        for (_, c) in &problem_state.clauses {
            if c.is_empty() {
                // println!("{:?}", (problem.decision_trail, problem.unit_trail, problem.pure_trail));
                return (false, problem_state);
            }
        }

        let (problem, l) = (self.heuristic)(problem_state);

        // self.pool.join(oper_a, oper_b);

        let results: Vec<(bool, ProblemState)> = [1, -1]
            .into_par_iter()
            .map(|sign| {
                let l = l * sign;
                let mut problem_clone = problem.clone();
                problem_clone.insert_clause(BTreeSet::from_iter(vec![l]));
                problem_clone.trails[0].push((l, problem.depth));
                self.dpll(problem_clone)
            })
            .collect::<Vec<(bool, ProblemState)>>();

        if results.clone()[0].0 {
            return results[0].clone();
        } else {
            return results[1].clone();
        }
    }
}

fn go_over_all_problems() {
    for heuristic in [moms, maximum_occurence, next_literal] {
        for num_threads in 10..=10 {
            let mut wtr = csv::Writer::from_writer(io::stdout());
            let _ = wtr.write_record([
                "problem_name",
                "vars",
                "clauses",
                "decision_type",
                "max_depth",
                "num_nodes",
                "duration_ms",
            ]);

            rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build_global()
                .unwrap();

            let problem_sets = fs::read_dir("problem_sets").unwrap();
            for problem_set in problem_sets {
                if vec![
                    "uf20-91",
                    "uf150-645",
                    "uf200-860",
                    // "uf250-1065",
                    "uf125-538",
                    "BMS_k3_n100_m429",
                    "uf50-218",
                    "uf100-430",
                    "uf225-960",
                ]
                .contains(&problem_set.as_ref().unwrap().file_name().to_str().unwrap())
                {
                    continue;
                } //

                let problem_set = fs::read_dir(problem_set.unwrap().path()).unwrap();
                println!("Problem set {:?}", problem_set);

                for problem in problem_set {
                    let start_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

                    let dpll = DPLL {
                        max_depth: Arc::new(Mutex::new(0)),
                        nodes: Arc::new(Mutex::new(0)),

                        heuristic: heuristic,
                    };

                    let problem_file = problem.unwrap().path();
                    print!("{:?}: \n", problem_file);
                    let problem = read_cnf(problem_file.to_str().unwrap());

                    let (sat, dpll_result) = dpll.dpll(problem.clone());
                    if sat {
                        let verification = verify_trail(problem, dpll_result.trails);

                        print!("{:?}", verification);
                    } else {
                        println!("claimed not sat");
                    }

                    let end_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                    print!(" {:?}ms\n", end_time.as_millis() - start_time.as_millis());
                }
            }
        }
    }
}

fn main() {
    go_over_all_problems();
}
