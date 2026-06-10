use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::Ordering::{Relaxed, SeqCst};
use std::sync::atomic::{AtomicBool, AtomicUsize};
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{fs, io, ops};

use rayon::iter::{IntoParallelIterator, ParallelIterator};

#[derive(Debug, Clone)]
// is only a single node in the recursion tree, does not in general (except the root node) represent the original problem
struct ProblemState {
    clauses: BTreeMap<usize, BTreeSet<isize>>, // indexed by usize, is a collection of literal names isizes
    literals: BTreeMap<isize, BTreeSet<usize>>, // named by isize, is a collection of indexes into 'clauses'

    clause_counter: usize, // for the dynamic adding of clauses; only increases; dead indices stay dead

    trails: [Vec<(isize, usize)>; 2], // trails of forced assignments (pure, unit) or decisions (heuristic) along a rollout in the recursive search tree

    depth: usize,
}

impl ProblemState {
    // dynamic insertion of clauses; not meaningful if cdcl is not implemented
    fn insert_clause(&mut self, clause: BTreeSet<isize>) {
        for var in &clause {
            if !self.literals.contains_key(var) {
                continue;
            }

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
fn read_cnf(file_path: &str) -> (ProblemState, usize, usize) {
    let contents = fs::read_to_string(file_path).expect("Couldn't read from file_path {file_path}");
    let contents = contents.split("cnf").collect::<Vec<&str>>();
    let contents = *contents.last().unwrap();
    let contents = contents.split_whitespace().collect::<Vec<&str>>();
    let mut contents = contents
        .into_iter()
        .filter_map(|x| x.parse().ok())
        .collect::<Vec<isize>>();

    let (num_vars, num_clauses) = (contents[0], contents[1]);
    contents.remove(0);
    contents.remove(0);

    let mut problem: ProblemState = ProblemState {
        clauses: BTreeMap::new(),
        literals: BTreeMap::from_iter(
            (-num_vars..=num_vars)
                .into_iter()
                .filter(|x| x != &0)
                .map(|i| (i, BTreeSet::new())),
        ),
        clause_counter: 0,

        trails: [vec![], vec![]],

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
    return (problem, num_vars as usize, num_clauses as usize);
}

// sanity, checks the trail if sat, if DPLL claims sat
fn verify_trail(problem_state: ProblemState, trails: [Vec<(isize, usize)>; 2]) -> bool {
    let assignments: BTreeSet<isize> = BTreeSet::from_iter(
        [trails[0].clone(), trails[1].clone()]
            .concat()
            .into_iter()
            .map(|x| x.0)
            .collect::<Vec<isize>>(),
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
fn find_unit(problem_state: &ProblemState) -> isize {
    for (_, c) in problem_state.clauses.iter() {
        if c.len() == 1 {
            return *c.iter().next().unwrap();
        }
    }
    return 0;
}

// propagates a found unit literal; does not check for correctness but assumes unit, likely malfunctions if asked to propagate non-unit
fn unit_propagate(l: isize, problem_state: &mut ProblemState) {
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
}

fn find_pure(problem_state: &ProblemState) -> isize {
    // returns the first pure literal, 0 if none
    for l in problem_state.literals.keys() {
        if problem_state.literals.get(&-l).unwrap().is_empty() {
            return *l;
        }
    }
    return 0;
}

// propagates a found pure literal; likely malfunctions in the same mode as unit_propagate
fn pure_propagate(l: isize, problem_state: &mut ProblemState) {
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

    problem_state.trails[0].push((l, problem_state.depth));
    problem_state.depth += 1;
}

// baseline literal decision, returns the next literal in the BTreeSet's (deterministic but arbitrary) iterator
fn next_literal(problem_state: &ProblemState) -> isize {
    let literal = &problem_state.literals.keys().next().unwrap().clone();
    *literal
}

struct ParametrizedMoms<const K: usize> {
    function: fn(problem_state: &ProblemState) -> isize,
}

impl<const K: usize> ParametrizedMoms<K> {
    fn parametrized_moms(problem_state: &ProblemState) -> isize {
        let mut min_length = *&problem_state.clauses.iter().next().unwrap().1.len();
        let mut smallest_clauses: Vec<usize> = vec![];

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

        let mut literal_counts: BTreeMap<isize, usize> = BTreeMap::new();
        for cindex in smallest_clauses {
            for literal in problem_state.clauses.get(&cindex).unwrap() {
                if !literal_counts.contains_key(literal) {
                    literal_counts.insert(*literal, 0);
                }
                *literal_counts.get_mut(literal).unwrap() += 1;
            }
        }

        let (mut max_literal, mut max) = (0, 0);

        for (literal, f_x) in &literal_counts {
            let f_notx = if literal_counts.contains_key(&-literal) {
                *literal_counts.get(&-literal).unwrap()
            } else {
                0
            };

            let score = (f_x + f_notx) * 2_usize.pow(K as u32) + (f_x * f_notx);

            if score > max {
                (max_literal, max) = (*literal, score)
            }
        }

        max_literal
    }
}

// maximum occurence of minimum size
fn moms(problem_state: &ProblemState) -> isize {
    let mut min_length = *&problem_state.clauses.iter().next().unwrap().1.len();
    let mut smallest_clauses: Vec<usize> = vec![];

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

    let mut literal_counts: BTreeMap<isize, usize> = BTreeMap::new();
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

    max_literal
}

struct DPLL {
    nodes: AtomicUsize,

    sat_found: AtomicBool,

    heuristic: fn(&ProblemState) -> isize,
}

impl DPLL {
    fn new(heuristic: fn(&ProblemState) -> isize) -> Self {
        DPLL {
            nodes: AtomicUsize::new(0),

            sat_found: AtomicBool::new(false),

            heuristic: heuristic,
        }
    }

    fn dpll(&self, mut problem_state: ProblemState) -> (bool, ProblemState) {
        if self.sat_found.load(Relaxed) {
            return (false, problem_state);
        }

        self.nodes.fetch_add(1, Relaxed);

        print!("\rNodes explored: {}", self.nodes.load(Relaxed),);

        problem_state.depth += 1;

        loop {
            let unit = find_unit(&problem_state);
            if unit == 0 {
                break;
            }

            unit_propagate(unit, &mut problem_state);
        }

        loop {
            let pure = find_pure(&problem_state);
            if pure == 0 {
                break;
            }

            pure_propagate(pure, &mut problem_state);
        }

        if problem_state.clauses.is_empty() {
            self.sat_found.store(true, Relaxed);
            return (true, problem_state);
        }
        for (_, c) in &problem_state.clauses {
            if c.is_empty() {
                return (false, problem_state);
            }
        }

        let l = (self.heuristic)(&problem_state);

        let results: Vec<(bool, ProblemState)> = [1, -1]
            .into_par_iter()
            .map(|sign: isize| {
                let l = l * sign;
                let mut problem_clone = problem_state.clone();
                problem_clone.insert_clause(BTreeSet::from_iter(vec![l]));
                self.dpll(problem_clone)
            })
            .collect();

        if results.clone()[0].0 {
            return results[0].clone();
        } else {
            return results[1].clone();
        }
    }
}

fn benchmark_problemsets(
    p_sets: Vec<&str>,
    heuristics: Vec<fn(&ProblemState) -> isize>,
    heur_names: Vec<&str>,
    nums_threads: Vec<usize>,
) {
    let mut wtr = csv::Writer::from_path(format!(
        "{:?}_{:?}_{:?}_results.csv",
        p_sets, heur_names, nums_threads
    ))
    .unwrap();
    let _ = wtr.write_record([
        "problem_name",
        "vars",
        "clauses",
        "decision_type",
        "num_threads",
        "num_nodes",
        "duration_mus",
    ]);

    for (heuristic, heur_name) in heuristics.into_iter().zip(heur_names) {
        for num_threads in nums_threads.iter() {
            rayon::ThreadPoolBuilder::new()
                .num_threads(*num_threads)
                .build()
                .unwrap();

            for problem_set in p_sets.iter() {
                let problem_set = fs::read_dir(format!("problem_sets/{}", problem_set)).unwrap();
                println!("Problem set {:?}", problem_set);

                for problem in problem_set {
                    let start_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

                    let dpll = DPLL::new(heuristic);

                    let problem_file = problem.unwrap().path();
                    print!("{:?}: \n", problem_file);
                    let (problem, num_vars, num_clauses) = read_cnf(problem_file.to_str().unwrap());

                    let (sat, dpll_result) = dpll.dpll(problem.clone());

                    if sat {
                        let verification = verify_trail(problem, dpll_result.trails);

                        print!("{:?}", verification);
                    } else {
                        println!("claimed not sat");
                    }

                    let end_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
                    let duration = (end_time - start_time).as_micros();
                    print!(" {:?}mus\n", duration);

                    let _ = wtr.write_record([
                        problem_file.file_name().unwrap().to_str().unwrap(),
                        &num_vars.to_string(),
                        &num_clauses.to_string(),
                        heur_name,
                        &num_threads.to_string(),
                        &dpll.nodes.load(Relaxed).to_string(),
                        &duration.to_string(),
                    ]);

                    let _ = wtr.flush();
                }
            }
        }
    }
}

fn benchmark_k() {
    macro_rules! benchmark_k {
        ($k: expr) => {
            benchmark_problemsets(
                vec![
                    // "uf175-753",
                    // "uf200-860",
                    // "uf225-960",
                    "uf250-1065",
                ],
                vec![ParametrizedMoms::<$k>::parametrized_moms],
                vec![&format!("MOMS_{}", $k)],
                vec![12],
            );
        };
    }

    const K1: usize = 1;
    benchmark_k!(K1);
    const K2: usize = 2;
    benchmark_k!(K2);
    const K3: usize = 3;
    benchmark_k!(K3);
    const K4: usize = 4;
    benchmark_k!(K4);
    const K5: usize = 5;
    benchmark_k!(K5);
    const K8: usize = 8;
    benchmark_k!(K8);
    const K10: usize = 10;
    benchmark_k!(K10);
    const K15: usize = 15;
    benchmark_k!(K15);
    const K20: usize = 20;
    benchmark_k!(K20);
}

fn time_problem(file_path: &str) {
    let start_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    let (problem, _, _) = read_cnf(file_path);
    let dpll = DPLL::new(ParametrizedMoms::<4>::parametrized_moms);
    let (sat, dpll_result) = dpll.dpll(problem.clone());

    if sat {
        let verification = verify_trail(problem, dpll_result.trails);

        print!("{:?}", verification);
    } else {
        println!("claimed not sat");
    }

    let end_time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    println!("{:?}", (end_time - start_time).as_secs());
}

fn main() {
    // benchmark_problemsets(vec!["f"], vec![moms], vec!["MOMS"], vec![12]);
    // benchmark_k();
    // benchmark_problemsets(vec!["uf20-91", "uf50-218", "uf75-325", "uf100-430", "uf125-538", "uf150-645", "uf175-753"], vec![moms, parametrized_moms, next_literal], vec!["MOMS", "MOMS_K", "arbitrary"], vec![12, 10, 8, 6, 4, 2, 1]);
    // benchmark_problemsets(
    //     vec!["uf250-1065"],
    //     vec![moms2],
    //     vec!["MOMS2"],
    //     vec![12],
    // );

    time_problem("problem_sets/f/f600.cnf");
}
