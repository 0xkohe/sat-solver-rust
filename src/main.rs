use std::vec;

#[derive(Clone,PartialEq,Debug)]
enum VarState {
    True,
    False,
    None,
}

fn propagete(x :&mut Vec<VarState>,cnf :& Vec<[Vec<usize>;2]>) -> bool {
    let mut done = false;
    while !done {
        done = true;
        for clause in cnf {
            let mut is: Vec<usize> = vec![];
            let p = &clause[0];
            let n = &clause[1];

            for i in 0..p.len() {
                if x[p[i]] != VarState::False  {
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

fn consistent(x :& Vec<VarState>,cnf :& Vec<[Vec<usize>;2]>) -> bool {
    for clause in cnf {
        let mut r = false;
        for i in 0..clause[0].len() {
            if x[clause[0][i]] != VarState::False  {
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

fn search<'a>(x:&'a mut Vec<VarState>, cnf :& Vec<[Vec<usize>;2]>) -> Option<&'a Vec<VarState>> {
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
            return Some(x);},
        None => (),
    }
    x[i] = VarState::False;
    search(x, cnf)
}

fn main() {
    let cnf = vec![
        // [true, not]
        [vec![],vec![2,3]],
        [vec![3],vec![0,2]],
        [vec![2,3],vec![]],
        [vec![2],vec![3]],
        [vec![0,1],vec![2]],
    ];
        let mut x = vec![VarState::None, VarState::None, VarState::None, VarState::None];
        let mut _x2 = vec![VarState::True, VarState::None, VarState::None, VarState::None];
        let mut _x3 = vec![VarState::False, VarState::False, VarState::True, VarState::None];
        println!("{:?}", search(&mut x, &cnf));

        //println!("{:?}",consistent(&x, &cnf));
        //println!("{:?}", propagete(&mut x, &cnf));
        //println!("{:?}", x);

        //println!("{:?}",consistent(&x2, &cnf));
        //println!("{:?}", propagete(&mut x2, &cnf));
        //println!("{:?}", x2);

        //println!("{:?}",consistent(&x3, &cnf));
        //println!("{:?}", propagete(&mut x3, &cnf));
        //println!("{:?}", x3);
}
