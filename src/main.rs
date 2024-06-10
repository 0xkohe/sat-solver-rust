use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fs::File;
use std::io::BufRead;
use std::vec;

#[derive(Clone, PartialEq, Debug)]
enum VarState {
    True,
    False,
    None,
}

struct Node {
    variable: usize,
    value: bool,
    decision_level: usize,
    antecedent: Option<Clause>,
}

#[derive(Clone, Debug)]
struct Clause {
    literals: Vec<Literal>,
    //watch: [usize; 2],
}

#[derive(Clone, Debug)]
struct Literal {
    variable: usize,
    nageted: bool,
}

struct ImplicationGraph {
    nodes: HashMap<usize, Node>,
    desitions: Vec<usize>,
}

impl ImplicationGraph {
    fn new() -> Self {
        ImplicationGraph {
            nodes: HashMap::new(),
            desitions: vec![],
        }
    }

    fn add_node(
        &mut self,
        variable: usize,
        value: bool,
        decision_level: usize,
        antecedent: Option<Clause>,
    ) {
        self.nodes.insert(
            variable,
            Node {
                variable,
                value,
                decision_level,
                antecedent,
            },
        );
        if decision_level == self.desitions.len() {
            self.desitions.push(variable);
        }
    }

    fn node(&self, variable: usize) -> Option<&Node> {
        self.nodes.get(&variable)
    }

    // TODO x should be propaty of the struct
    fn backtrack(&mut self, decision_level: usize, x: &mut Vec<VarState>) {
        let mut to_remove = vec![];
        for (variable, node) in &self.nodes {
            if node.decision_level >= decision_level {
                to_remove.push(*variable);
                x[*variable] = VarState::None;
            }
        }
        for variable in to_remove {
            self.nodes.remove(&variable);
        }
        self.desitions.truncate(decision_level);
    }
    fn analyze(&self, conflict_clause: Clause) -> (Clause, usize) {
        let mut learned_clause = conflict_clause.clone();
        let mut seen: HashSet<usize> = HashSet::new();
        // for BFS
        let mut que: VecDeque<Literal> = VecDeque::new();
        let mut backtrack_level = 0;

        // to check the nodes levels, if it contains one literal in the current literal, finish
        // let mut diagnose_nodes: HashSet<usize> = HashSet::new();
        // 初期スタックに矛盾節のリテラルを追加
        for literal in &conflict_clause.literals {
            que.push_front(literal.clone());
        }

        // while let Some(literal) = que.pop_back() {
        loop {
            if que.len() == 1 {
                backtrack_level = 0;
                break;
            }

            {
                let mut i = 0;
                let mut second_highest = 0;
                for lit_v in &que {
                    if let Some(node) = self.node(lit_v.variable) {
                        if node.decision_level == self.desitions.len() {
                            i += 1;
                            if i > 1 {
                                break;
                            }
                        } else {
                            if node.decision_level > second_highest {
                                second_highest = node.decision_level;
                            }
                        }
                    }
                }
                // check if it contains only one literal in the current decision level
                if i == 1 {
                    backtrack_level = second_highest;
                    break;
                }
            }
            if let Some(literal) = que.pop_back() {
                if let Some(node) = self.node(literal.variable) {
                    if seen.contains(&literal.variable) {
                        continue;
                    }
                    seen.insert(literal.variable);

                    if let Some(antecedent) = &node.antecedent {
                        for ante_lit in &antecedent.literals {
                            if !seen.contains(&ante_lit.variable) {
                                que.push_front(ante_lit.clone());
                            }
                        }
                    }
                } else {
                    // make error
                    break;
                }
            } else {
                // make error
                break;
            }
        }

        for lit_v in &que {
            if let Some(node) = self.node(lit_v.variable) {
                learned_clause.literals.push(Literal {
                    variable: lit_v.variable,
                    nageted: !node.value,
                });
            }
        }

        (learned_clause, backtrack_level)
    }
}

#[allow(dead_code)]
fn propagete(x: &mut Vec<VarState>, cnf: &Vec<Clause>) -> bool {
    let mut done = false;
    while !done {
        done = true;
        for clause in cnf {
            let mut is: Vec<usize> = vec![];

            for lit in &clause.literals {
                let i = lit.variable;
                if lit.nageted {
                    if x[i] != VarState::True {
                        is.push(i);
                    }
                } else {
                    if x[i] != VarState::False {
                        is.push(i);
                    }
                }
            }

            let i = match is.pop() {
                Some(i) => i,
                None => return false,
            };
            if is.len() == 0 && x[i] == VarState::None {
                let t = match clause.literals.iter().find(|x| x.variable == i) {
                    Some(t) => t,
                    None => return false,
                };

                if t.nageted {
                    x[i] = VarState::False;
                } else {
                    x[i] = VarState::True;
                }
                done = false;
            }
        }
    }
    true
}

enum Conflict {
    Yes(Clause),
    No,
}

fn unit_propagete(
    x: &mut Vec<VarState>,
    cnf: &Vec<Clause>,
    decision_level: usize,
    i_graph: &mut ImplicationGraph,
) -> Conflict {
    let mut done = false;
    while !done {
        done = true;
        for clause in cnf {
            let mut is: Vec<usize> = vec![];

            for lit in &clause.literals {
                let i = lit.variable;
                if lit.nageted {
                    if x[i] != VarState::True {
                        is.push(i);
                    }
                } else {
                    if x[i] != VarState::False {
                        is.push(i);
                    }
                }
            }

            let ii = match is.pop() {
                Some(i) => i,
                None => return Conflict::Yes(clause.clone()),
            };
            if is.len() == 0 && x[ii] == VarState::None {
                let t_lit = match clause.literals.iter().find(|x| x.variable == ii) {
                    Some(t) => t,
                    //TODO
                    None => return Conflict::No,
                };

                if t_lit.nageted {
                    x[ii] = VarState::False;
                } else {
                    x[ii] = VarState::True;
                }

                // TODO: clause should be refferenced
                i_graph.add_node(
                    ii,
                    x[ii] == VarState::True,
                    decision_level,
                    Some(clause.clone()),
                );
                done = false;
            }
        }
    }
    Conflict::No
}

fn solve(x: &mut Vec<VarState>, cnf: &mut Vec<Clause>) -> Option<bool> {
    let mut desicion_level = 0_usize;
    let mut i_grapgh = ImplicationGraph::new();
    loop {
        // no conflict
        if let Conflict::Yes(conflict_clause) =
            unit_propagete(x, cnf, desicion_level, &mut i_grapgh)
        {
            let (learned_clause, backtrack_level) = i_grapgh.analyze(conflict_clause);
            if backtrack_level == 0 {
                return Some(false);
            }
            cnf.push(learned_clause);
            i_grapgh.backtrack(backtrack_level, x);
            desicion_level = backtrack_level;
        } else {
            let i = match x.iter().position(|x| *x == VarState::None) {
                Some(i) => i,
                None => return Some(true),
            };
            desicion_level += 1;
            x[i] = VarState::False;
            i_grapgh.add_node(i, true, desicion_level, None);
        }
    }
}

#[allow(dead_code)]
fn search<'a>(x: &'a mut Vec<VarState>, cnf: &Vec<Clause>) -> Option<&'a Vec<VarState>> {
    if !propagete(x, cnf) {
        return None;
    }
    let i = match x.iter().position(|x| *x == VarState::None) {
        Some(i) => i,
        None => return Some(x),
    };
    let mut y = x.clone();
    y[i] = VarState::True;
    match search(&mut y, cnf) {
        Some(z) => {
            *x = z.clone();
            return Some(x);
        }
        None => (),
    }
    x[i] = VarState::False;
    search(x, cnf)
}

fn read_file(path: &str) -> std::result::Result<(Vec<Clause>, usize), std::io::Error> {
    use std::io::BufReader;
    let f = File::open(&path)?;
    let reader = BufReader::new(f);
    // let mut cnf: Vec<[Vec<usize>; 2]> = vec![];
    let mut cnf: Vec<Clause> = Vec::new();
    let mut n_v: usize = 0;
    for (i, line) in reader.lines().enumerate() {
        if i == 0 {
            n_v = line?.split_whitespace().nth(2).unwrap().parse().unwrap();
            continue;
        }
        let row: Vec<i32> = line?
            .split_whitespace()
            .filter(|x| *x != "0")
            .map(|x: &str| -> i32 { x.parse().unwrap() })
            .collect();
        let mut c = Clause { literals: vec![] };
        for x in row {
            if x > 0 {
                c.literals.push(Literal {
                    variable: (x - 1) as usize,
                    nageted: false,
                });
            } else {
                c.literals.push(Literal {
                    variable: (-x - 1) as usize,
                    nageted: true,
                });
            }
        }
        cnf.push(c);
    }

    Ok((cnf, n_v))
}

fn main() -> std::result::Result<(), std::io::Error> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <cnf file>", args[0]);
        std::process::exit(2);
    }

    let path = &args[1];
    let f_i = read_file(path)?;
    let mut cnf = f_i.0;
    let mut x = vec![VarState::None; f_i.1];

    match solve(&mut x, &mut cnf) {
        Some(r) => {
            if r {
                println!("s SATISFIABLE");
                print!("v ");
            } else {
                println!("s UNSATISFIABLE");
                return Ok(());
            }
        }
        None => {
            println!("s UNSATISFIABLE");
            return Ok(());
        }
    };

    for i in 0..x.len() {
        if x[i] == VarState::True {
            print!("{} ", i + 1);
        } else {
            print!("-{} ", i + 1);
        }
    }
    print!("{}", 0);

    Ok(())
}
