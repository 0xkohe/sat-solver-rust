use std::vec;

#[derive(Clone,PartialEq,Debug)]
enum VarState {
    True,
    False,
    None,
}
fn consistent(x :& Vec<VarState>,cnf :& Vec<[Vec<usize>;2]>) -> bool {
    for clause in cnf {
        let mut r = false;
        for i in 0..clause[0].len() {
            // println!("left {} {:?}",clause[0][i],x[clause[0][i]]);
            if x[clause[0][i]] != VarState::False  {
                r = true;
                break;
            }
        }
        for i in 0..clause[1].len() {
            // println!("right {} {:?}",clause[1][i],x[clause[1][i]]);
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
    if !consistent(x, cnf) {
        return None;
    }
    let i = match x.iter().position(|x| *x == VarState::None) {
        Some(i) => i,
        None => return Some(x),
    };
    println!("{}", i);
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
        //let mut y = vec![VarState::True, VarState::None, VarState::None, VarState::None];
        //let mut z = vec![VarState::False, VarState::True, VarState::True, VarState::False];
        println!("{:?}", search(&mut x, &cnf));
        // println!("{:?}", consistent(&x, &cnf));
        // println!("{:?}", consistent(&y, &cnf));
        //println!("{:?}", consistent(&z, &cnf));
}
