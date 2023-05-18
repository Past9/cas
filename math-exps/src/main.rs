use std::cmp::Ordering;
use std::collections::HashMap;

use cas_core::ast::helpers::*;
use cas_core::ast::Ast;

fn main() {
    let points = vec![[1, 0], [1, 1], [0, 1], [0, 0]];

    let mut bez = Ast::bezier(vec![sym("p0"), sym("p1"), sym("p2"), sym("p3")]);
    println!("bez1: {:?}", bez);

    let mut bezx = bez
        .clone()
        .substitute(&sym("p0"), points[0][0].into())
        .substitute(&sym("p1"), points[1][0].into())
        .substitute(&sym("p2"), points[2][0].into())
        .substitute(&sym("p3"), points[3][0].into());

    println!("bezx: {:?}", bezx);

    for t in 0..=10 {
        let t = frc(t as i128, 10);
        let bezx = bezx.clone().substitute(&sym("t"), t.clone());
        println!("bezx @ t = {:?}: {:?}", t, bezx);
    }

    let mut bezy = bez
        .substitute(&sym("p0"), points[0][1].into())
        .substitute(&sym("p1"), points[1][1].into())
        .substitute(&sym("p2"), points[2][1].into())
        .substitute(&sym("p3"), points[3][1].into());

    println!("bezy: {:?}", bezy);

    for t in 0..=10 {
        let t = frc(t as i128, 10);
        let bezy = bezy.clone().substitute(&sym("t"), t.clone());
        println!("bezx @ t = {:?}: {:?}", t, bezy);
    }
}
