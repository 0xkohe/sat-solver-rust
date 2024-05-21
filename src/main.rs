use std::fs::File;
use std::io::BufRead;
use std::vec;

#[derive(Clone, PartialEq, Debug)]
enum VarState {
    True,
    False,
    None,
}

fn propagete(x: &mut Vec<VarState>, cnf: &Vec<[Vec<usize>; 2]>) -> bool {
    let mut done = false;
    while !done {
        done = true;
        for clause in cnf {
            let mut is: Vec<usize> = vec![];
            let p = &clause[0];
            let n = &clause[1];

            for i in 0..p.len() {
                if x[p[i]] != VarState::False {
                    is.push(p[i]);
                }
            }
            for i in 0..n.len() {
                if x[n[i]] != VarState::True {
                    is.push(n[i]);
                }
            }

            let i = match is.pop() {
                Some(i) => i,
                None => return false,
            };
            if is.len() == 0 && x[i] == VarState::None {
                if p.contains(&i) {
                    x[i] = VarState::True;
                } else {
                    x[i] = VarState::False;
                }
                done = false;
            }
        }
    }
    true
}

fn consistent(x: &Vec<VarState>, cnf: &Vec<[Vec<usize>; 2]>) -> bool {
    for clause in cnf {
        let mut r = false;
        for i in 0..clause[0].len() {
            if x[clause[0][i]] != VarState::False {
                r = true;
                break;
            }
        }
        if r {
            continue;
        }
        for i in 0..clause[1].len() {
            if x[clause[1][i]] != VarState::True {
                r = true;
                break;
            }
        }
        if !r {
            return false;
        }
    }
    true
}

fn search<'a>(x: &'a mut Vec<VarState>, cnf: &Vec<[Vec<usize>; 2]>) -> Option<&'a Vec<VarState>> {
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

fn read_file(path: &str) -> std::result::Result<(Vec<[Vec<usize>; 2]>,usize), std::io::Error> {
    use std::io::BufReader;
    let f = File::open(&path)?;
    let reader = BufReader::new(f);
    let mut cnf: Vec<[Vec<usize>; 2]> = vec![];
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
        let mut c: [Vec<usize>; 2] = [vec![], vec![]];
        for x in row {
            if x > 0 {
                c[0].push((x - 1) as usize);
            } else {
                c[1].push((-x - 1) as usize);
            }
        }
        cnf.push(c);
    }

    Ok((cnf, n_v))
}

fn main() -> std::result::Result<(), std::io::Error>{
    /*
    let cnf = vec![
        // [true, not]
        [vec![], vec![2, 3]],
        [vec![3], vec![0, 2]],
        [vec![2, 3], vec![]],
        [vec![2], vec![3]],
        [vec![0, 1], vec![2]],
    ];
    let mut x = vec![
        VarState::None,
        VarState::None,
        VarState::None,
        VarState::None,
    ];
    let mut _x2 = vec![
        VarState::True,
        VarState::None,
        VarState::None,
        VarState::None,
    ];
    let mut _x3 = vec![
        VarState::False,
        VarState::False,
        VarState::True,
        VarState::None,
    ];
    println!("{:?}", search(&mut x, &cnf));
    //println!("{:?}", read_file("sudoku.cnf"));
    */

    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <cnf file>", args[0]);
        std::process::exit(1);
    }

    let path = &args[1];
    let f_i = read_file(path)?;
    let cnf = f_i.0;
    let mut x = vec![VarState::None; f_i.1];
    //println!("{:?}", search(&mut x, &cnf));
    
    let r = match search(&mut x, &cnf) {
        Some(r) => {
            println!("s SATISFIABLE");
            print!("v ");
            r
        } ,
        None => {
            println!("s UNSATISFIABLE");
            return Ok(())} ,
    };
    for i in 0..r.len()  {
        if r[i] == VarState::True {
            print!("{} ", i+1);
        } else {
            print!("-{} ", i+1);
        }
    }
    print!("{}", 0);

    Ok(())
}
