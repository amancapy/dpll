use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io};

use rayon::iter::{IntoParallelIterator, ParallelIterator};

#[derive(Debug, Clone)]
struct ProblemState {
    clauses: BTreeMap<u64, BTreeSet<i64>>,
    literals: BTreeMap<i64, BTreeSet<u64>>,

    clause_counter: u64,

    trails: [Vec<(i64, u64)>; 3],

    depth: u64,
}

impl ProblemState {
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

fn verify_trail(problem: ProblemState, trails: [Vec<(i64, u64)>; 3]) -> bool {
    let assignments: BTreeSet<i64> = BTreeSet::from_iter(
        [trails[1].clone(), trails[2].clone()]
            .concat()
            .into_iter()
            .map(|x| x.0)
            .collect::<Vec<i64>>(),
    );

    // println!("{:?}", assignments);

    'outer: for (_, clause) in problem.clauses {
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

fn find_unit(problem: &ProblemState) -> i64 {
    for (_, c) in problem.clauses.iter() {
        if c.len() == 1 {
            return *c.iter().next().unwrap();
        }
    }
    return 0;
}

fn unit_propagate(l: i64, mut problem: ProblemState) -> ProblemState {
    for cidx in problem.literals.get_mut(&l).cloned().unwrap() {
        let removed_clause = problem.clauses.remove(&cidx).unwrap();
        for literal in removed_clause {
            problem.literals.get_mut(&literal).unwrap().remove(&cidx);
        }
    }
    for cidx in problem.literals.get_mut(&-l).cloned().unwrap() {
        problem.clauses.get_mut(&cidx).unwrap().remove(&-l);
    }

    problem.literals.remove(&l);
    problem.literals.remove(&-l);

    problem.trails[1].push((l, problem.depth));
    problem.depth += 1;

    return problem;
}

fn find_pure(problem: &ProblemState) -> i64 {
    for l in problem.literals.keys() {
        if problem.literals.get(&-l).unwrap().is_empty() {
            return *l;
        }
    }
    return 0;
}

fn pure_propagate(l: i64, mut problem: ProblemState) -> ProblemState {
    for lc in [l, -l] {
        {
            for cidx in problem.literals.get_mut(&lc).cloned().unwrap() {
                let removed_clause = problem.clauses.remove(&cidx).unwrap();
                for literal in removed_clause {
                    problem.literals.get_mut(&literal).unwrap().remove(&cidx);
                }
            }
            problem.literals.remove(&lc);
        }
    }

    problem.trails[2].push((l, problem.depth));
    problem.depth += 1;

    return problem;
}

struct DPLL {
    nodes: Arc<Mutex<u64>>,
    max_depth: Arc<Mutex<u64>>,
}

impl DPLL {
    fn dpll(&self, mut problem: ProblemState) -> (bool, ProblemState) {
        *self.nodes.lock().unwrap() += 1;
        print!(
            "\rNodes explored: {}, Max depth reached: {} ",
            *self.nodes.lock().unwrap(),
            *self.max_depth.lock().unwrap()
        );

        problem.depth += 1;
        if problem.depth > *self.max_depth.lock().unwrap() {
            *self.max_depth.lock().unwrap() = problem.depth;
        }

        loop {
            let unit = find_unit(&problem);
            if unit == 0 {
                break;
            }

            problem = unit_propagate(unit, problem);
        }

        loop {
            let pure = find_pure(&problem);
            if pure == 0 {
                break;
            }

            problem = pure_propagate(pure, problem);
        }

        if problem.clauses.is_empty() {
            // println!("{:?}", (problem.decision_trail, problem.unit_trail, problem.pure_trail));
            return (true, problem);
        }
        for (_, c) in &problem.clauses {
            if c.is_empty() {
                // println!("{:?}", (problem.decision_trail, problem.unit_trail, problem.pure_trail));
                return (false, problem);
            }
        }

        let l = problem.literals.keys().next().unwrap();

        // self.pool.join(oper_a, oper_b);

        let results: Vec<(bool, ProblemState)> = [1, -1]
            .into_par_iter()
            .map(|sign| {
                let l = *l * sign;
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
    for num_threads in 11..=12 {
        let mut wtr = csv::Writer::from_writer(io::stdout());
        wtr.write_record([
            "problem_name",
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
            if vec!["uf225-960", "uf200-860"]
                .contains(&problem_set.as_ref().unwrap().file_name().to_str().unwrap())
            {
                continue;
            }

            let problem_set = fs::read_dir(problem_set.unwrap().path()).unwrap();
            println!("Problem set {:?}", problem_set);

            for problem in problem_set {
                let start_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

                let dpll = DPLL {
                    max_depth: Arc::new(Mutex::new(0)),
                    nodes: Arc::new(Mutex::new(0)),
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

fn main() {
    go_over_all_problems();
}
