use std::fs;
use std::{
    clone,
    collections::{HashMap, HashSet},
    os::unix::process,
};

#[derive(Debug, Clone)]
struct Problem {
    clauses: HashMap<u64, HashSet<i64>>,
    literals: HashMap<i64, HashSet<u64>>,

    clause_counter: u64,

    trails: [Vec<(i64, u64)>; 3],

    depth: u64,
}

impl Problem {
    fn insert_clause(&mut self, clause: HashSet<i64>) {
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

fn read_cnf(file_path: &str) -> Problem {
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

    let mut problem: Problem = Problem {
        clauses: HashMap::new(),
        literals: HashMap::from_iter(
            (-num_vars..=num_vars)
                .into_iter()
                .filter(|x| x != &0)
                .map(|i| (i, HashSet::new())),
        ),
        clause_counter: 0,

        trails: [vec![], vec![], vec![]],

        depth: 0,
    };

    let mut clause = HashSet::new();
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

fn verify_trail(problem: Problem, trails: [Vec<(i64, u64)>; 3]) -> bool {
    let assignments: HashSet<i64> = HashSet::from_iter(
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

fn find_unit(problem: &Problem) -> i64 {
    for (_, c) in problem.clauses.iter() {
        if c.len() == 1 {
            return *c.iter().next().unwrap();
        }
    }
    return 0;
}

fn unit_propagate(l: i64, mut problem: Problem) -> Problem {
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

fn find_pure(problem: &Problem) -> i64 {
    for l in problem.literals.keys() {
        if problem.literals.get(&-l).unwrap().is_empty() {
            return *l;
        }
    }
    return 0;
}

fn pure_propagate(l: i64, mut problem: Problem) -> Problem {
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

fn dpll(mut problem: Problem) -> (bool, Problem) {
    // problem.depth += 1;

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
    let mut problem_clone = problem.clone();
    problem_clone.insert_clause(HashSet::from_iter(vec![*l]));
    problem_clone.trails[0].push((*l, problem.depth));
    let positive_result = dpll(problem_clone);
    if positive_result.0 {
        return positive_result;
    } else {
        let mut problem_clone = problem.clone();
        problem_clone.insert_clause(HashSet::from_iter(vec![-*l]));
        problem_clone.trails[0].push((-*l, problem.depth));
        return dpll(problem_clone);
    }
}

fn go_over_all_problems(dir: String) {
    let paths = fs::read_dir(dir).unwrap();
    for path in paths {
        print!("{:?} | ", path.as_ref().unwrap().path().to_str().unwrap());
        // println!("{:?}", path.unwrap().file_name());
        let problem = read_cnf(path.as_ref().unwrap().path().to_str().unwrap());
        let (sat, dpll_result) = dpll(problem.clone());
        let verification = verify_trail(problem, dpll_result.trails);

        println!("{:?}", verification);
    }
}

fn main() {
    go_over_all_problems("uf20-91".to_string());
}
