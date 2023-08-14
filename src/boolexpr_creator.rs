// boolexpr_creator.rs - boolean expression creator.
//
// cnfgen - Generate the DIMACS CNF formulae from operations
// Copyright (C) 2022  Mateusz Szpakowski
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module to generate CNF clauses from boolean expressions.
//!
//! It defines the ExprCreator - main structure to create and hold boolean expressions.

use std::cell::RefCell;
use std::fmt::Debug;
use std::io::Write;
use std::ops::Neg;
use std::rc::Rc;

use crate::gate::{Literal, VarLit};

#[cfg(test)]
macro_rules! test_println {
    () => { println!(); };
    ($($arg:tt)*) => { println!($($arg)*); };
}

#[cfg(not(test))]
macro_rules! test_println {
    () => {};
    ($($arg:tt)*) => {};
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Node<T: VarLit + Debug> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
    Impl(usize, usize),
}

impl<T: VarLit + Debug> Node<T> {
    fn first_path(&self) -> usize {
        match *self {
            Node::Single(_) => panic!("No first path for single node"),
            Node::Negated(first) => first,
            Node::And(first, _) => first,
            Node::Or(first, _) => first,
            Node::Xor(first, _) => first,
            Node::Equal(first, _) => first,
            Node::Impl(first, _) => first,
        }
    }

    fn second_path(&self) -> usize {
        match *self {
            Node::And(_, second) => second,
            Node::Or(_, second) => second,
            Node::Xor(_, second) => second,
            Node::Equal(_, second) => second,
            Node::Impl(_, second) => second,
            _ => panic!("No second path for single node"),
        }
    }

    #[inline]
    fn is_single(&self) -> bool {
        matches!(self, Node::Single(_))
    }

    #[inline]
    fn is_negated(&self) -> bool {
        matches!(self, Node::Negated(_))
    }

    #[inline]
    fn is_unary(&self) -> bool {
        matches!(self, Node::Single(_) | Node::Negated(_))
    }

    /// Returns true if node represents And operation.
    #[inline]
    fn is_conj(&self) -> bool {
        matches!(self, Node::And(_, _))
    }

    /// Returns true if node represents Or or Implication operation.
    #[inline]
    fn is_disjunc(&self) -> bool {
        matches!(self, Node::Or(_, _) | Node::Impl(_, _))
    }

    #[inline]
    fn is_xor_or_equal(&self) -> bool {
        matches!(self, Node::Xor(_, _) | Node::Equal(_, _))
    }
}

// internals
#[derive(Copy, Clone, Debug)]
struct DepNode<T: VarLit + Debug> {
    normal_usage: bool,
    negated_usage: bool,
    linkvar: Option<T>,
    parent_count: usize,
}

impl<T: VarLit + Debug> Default for DepNode<T> {
    #[inline]
    fn default() -> Self {
        DepNode {
            normal_usage: false,
            negated_usage: false,
            linkvar: None,
            parent_count: 0,
        }
    }
}

// Operation join -
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpJoin {
    Nothing,
    Conj,    // if tree of conjunctions
    Disjunc, // if tree of disjunctions
}

/// The ExprCreator holds all expressions which will be written later.
///
/// Main purpose of ExprCreator is maintenance state of expression with its variables
/// during creating that expression by using ExprNode.
/// An ExprCreator is used with ExprNode to create new expression.
///
/// The generic parameter T is variable literal type - it can be signed integer.
#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit + Debug> {
    pub(super) nodes: Vec<Node<T>>,
    pub(super) lit_to_index: Vec<usize>,
}

// macro to create new_* methods for ExprCreator.
macro_rules! new_xxx {
    ($t:ident, $u:ident) => {
        pub(super) fn $t(&mut self, a_index: usize, b_index: usize) -> usize {
            assert!(a_index < self.nodes.len());
            assert!(b_index < self.nodes.len());
            self.nodes.push(Node::$u(a_index, b_index));
            self.nodes.len() - 1
        }
    };
}

impl<T> ExprCreator<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates new ExprCreator as returns it as RefCounter.
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: vec![],
        }))
    }

    /// Returns variable count.
    #[inline]
    pub fn var_count(&self) -> T {
        T::from_usize(self.lit_to_index.len() >> 1)
    }

    pub(super) fn new_variable(&mut self) -> Literal<T> {
        self.lit_to_index.push(0); // zero - no variable
        self.lit_to_index.push(0);
        Literal::from(self.var_count())
    }

    pub(super) fn single(&mut self, l: impl Into<Literal<T>>) -> usize {
        match l.into() {
            Literal::Value(false) => 0,
            Literal::Value(true) => 1,
            Literal::VarLit(ll) => {
                assert!(ll.positive().unwrap() <= self.var_count());
                let ltoi =
                    ((ll.positive().unwrap().to_usize() - 1) << 1) + usize::from(ll < T::empty());
                let node_index = self.lit_to_index[ltoi];
                if node_index != 0 {
                    node_index
                } else {
                    self.nodes.push(Node::Single(Literal::VarLit(ll)));
                    self.lit_to_index[ltoi] = self.nodes.len() - 1;
                    self.nodes.len() - 1
                }
            }
        }
    }

    pub(super) fn new_not(&mut self, index: usize) -> usize {
        assert!(index < self.nodes.len());
        self.nodes.push(Node::Negated(index));
        self.nodes.len() - 1
    }

    new_xxx!(new_and, And);
    new_xxx!(new_or, Or);
    new_xxx!(new_xor, Xor);
    new_xxx!(new_equal, Equal);
    new_xxx!(new_impl, Impl);
}

// types

/// Typical `ExprCreator` defined with 32-bit variable literals.
pub type ExprCreator32 = ExprCreator<i32>;
/// Typical `ExprCreator` defined with pointer sized variable literals.
pub type ExprCreatorSys = ExprCreator<isize>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::{BoolEqual, BoolExprNode, BoolImpl};
    use crate::intexpr::{IntEqual, IntExprNode, IntOrd};

    macro_rules! expr_creator_testcase {
        ($ec: ident, $v: ident, $vars: expr, $expr: tt, $res: expr) => {
            let empty: [(Quantifier, Vec<isize>); 0] = [];
            expr_creator_testcase!($ec, $v, $vars, $expr, empty, $res);
        };

        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $quants: expr, $res: expr) => {
            $ec = ExprCreator::<isize>::new();
            $v.clear();
            $v.push(BoolExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(BoolExprNode::variable($ec.clone()));
            }
            let expr_index = $expr;
            let mut cnf_writer = CNFWriter::new(vec![]);
            test_println!("expr: {}", expr_index);
            $ec.borrow()
                .write(expr_index, $quants, &mut cnf_writer)
                .unwrap();
            assert_eq!($res, String::from_utf8_lossy(cnf_writer.inner()));
        };
    }

    #[test]
    fn test_expr_creator_trivial() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // single operator testcases
        expr_creator_testcase!(ec, v, 1, { 0 }, "p cnf 1 1\n0\n");
        expr_creator_testcase!(ec, v, 1, { v[1].index }, "p cnf 1 0\n");
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() & v[2].clone()).index },
            concat!("p cnf 2 2\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() | v[2].clone()).index },
            concat!("p cnf 2 1\n", "1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().imp(v[2].clone())).index },
            concat!("p cnf 2 1\n", "-1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() ^ v[2].clone()).index },
            concat!("p cnf 2 2\n", "1 2 0\n-1 -2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().bequal(v[2].clone())).index },
            concat!("p cnf 2 2\n", "1 -2 0\n-1 2 0\n")
        );

        // negation at root
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() & v[2].clone())).index },
            concat!("p cnf 2 1\n", "-1 -2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() & v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 2\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() | v[2].clone())).index },
            concat!("p cnf 2 2\n", "-1 0\n-2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() | v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 1\n", "1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() ^ v[2].clone())).index },
            concat!("p cnf 2 2\n", "1 -2 0\n-1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 2\n", "1 2 0\n-1 -2 0\n")
        );

        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let mut ec = ec.borrow_mut();
                let nv1 = ec.new_not(v[1].index);
                ec.new_and(nv1, v[2].index)
            },
            concat!("p cnf 2 2\n", "-1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let mut ec = ec.borrow_mut();
                let nv1 = ec.new_not(v[1].index);
                let nnv1 = ec.new_not(nv1);
                ec.new_and(v[2].index, nnv1)
            },
            concat!("p cnf 2 2\n", "2 0\n1 0\n")
        );
    }

    #[test]
    fn test_expr_creator_simple() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // simple testcases
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) | (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) & (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 6\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 0\n5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()).imp(v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((!(v[1].clone() ^ v[2].clone())) | (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[2].clone().bequal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                let xp1 = ec.new_not(xp1);
                ec.new_or(xp1, xp2.index)
            },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((!(v[1].clone() ^ v[2].clone())).imp(v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[2].clone().bequal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                let xp1 = ec.new_not(xp1);
                ec.new_impl(xp1, xp2.index)
            },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) ^ (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 10\n",
                "1 2 -4 0\n-1 -2 -4 0\n1 -2 4 0\n-1 2 4 0\n",
                "2 -3 -5 0\n-2 3 -5 0\n2 3 5 0\n-2 -3 5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() & v[2].clone()) ^ (v[2].clone() & v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()) ^ (v[2].clone() | v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() & v[2].clone()).bequal(v[2].clone() & v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()).bequal(v[2].clone() | v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 -5 0\n-4 5 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_more_complex() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // more complicated, but simple
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) | (v[3].clone() ^ v[4].clone()))
                    | ((v[5].clone() ^ v[6].clone()) | (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 9\n",
                "1 2 -9 0\n-1 -2 -9 0\n3 4 -10 0\n-3 -4 -10 0\n5 6 -11 0\n-5 -6 -11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n9 10 11 12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) & (v[3].clone() ^ v[4].clone()))
                    & ((v[5].clone() ^ v[6].clone()) & (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 12\n",
                "1 2 -9 0\n-1 -2 -9 0\n3 4 -10 0\n-3 -4 -10 0\n5 6 -11 0\n-5 -6 -11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n9 0\n10 0\n11 0\n12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()).imp(v[3].clone() ^ v[4].clone()))
                    | ((v[5].clone() ^ v[6].clone()).imp(v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 9\n",
                "1 -2 9 0\n-1 2 9 0\n3 4 -10 0\n-3 -4 -10 0\n5 -6 11 0\n-5 6 11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n-9 10 -11 12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) | (v[3].clone() ^ v[4].clone()))
                    .imp((v[5].clone() ^ v[6].clone()) | (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 13 11\n",
                "1 -2 10 0\n-1 2 10 0\n3 -4 11 0\n-3 4 11 0\n9 -10 0\n9 -11 0\n",
                "5 6 -12 0\n-5 -6 -12 0\n7 8 -13 0\n-7 -8 -13 0\n-9 12 13 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) ^ (v[3].clone() ^ v[4].clone()))
                    ^ ((v[5].clone() ^ v[6].clone()) ^ (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 14 26\n",
                "1 2 -10 0\n-1 -2 -10 0\n1 -2 10 0\n-1 2 10 0\n",
                "3 4 -11 0\n-3 -4 -11 0\n3 -4 11 0\n-3 4 11 0\n",
                "-9 10 11 0\n-9 -10 -11 0\n9 10 -11 0\n9 -10 11 0\n",
                "5 6 -13 0\n-5 -6 -13 0\n5 -6 13 0\n-5 6 13 0\n",
                "7 8 -14 0\n-7 -8 -14 0\n7 -8 14 0\n-7 8 14 0\n",
                "-12 13 14 0\n-12 -13 -14 0\n12 13 -14 0\n12 -13 14 0\n",
                "9 12 0\n-9 -12 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_join_more_time() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | (xp1 & xp2)).index
            },
            concat!(
                "p cnf 7 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n3 4 -6 0\n-3 -4 -6 0\n5 -7 0\n6 -7 0\n5 6 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | !(xp1 & xp2)).index
            },
            concat!(
                "p cnf 7 10\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n",
                "3 4 -6 0\n-3 -4 -6 0\n3 -4 6 0\n-3 4 6 0\n",
                "-5 -6 7 0\n5 6 -7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | (xp1.imp(xp2))).index
            },
            concat!(
                "p cnf 6 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n3 4 -6 0\n-3 -4 -6 0\n1 -1 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | ((!xp1) | xp2)).index
            },
            concat!(
                "p cnf 6 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n3 4 -6 0\n-3 -4 -6 0\n1 -1 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) & (xp1.imp(xp2))).index
            },
            concat!(
                "p cnf 8 10\n",
                "1 2 -6 0\n-1 -2 -6 0\n1 -2 6 0\n-1 2 6 0\n3 4 -7 0\n-3 -4 -7 0\n",
                "-5 6 7 0\n-6 7 -8 0\n5 0\n8 0\n"
            )
        );

        // not joining
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            concat!("p cnf 7 4\n", "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            { (!((v[1].clone() | v[2].clone()).imp(v[2].clone())) | v[3].clone()).index },
            concat!("p cnf 6 4\n", "1 2 -6 0\n5 6 0\n-2 5 0\n3 -5 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()) | (v[3].clone())) | v[4].clone()).index },
            concat!("p cnf 6 4\n", "-1 6 0\n-2 6 0\n-3 6 0\n4 -6 0\n")
        );

        // joinings of conjunction and disjunction
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) & (xp1 | v[4].clone())).index
            },
            concat!("p cnf 7 5\n", "1 2 -6 0\n3 -5 6 0\n4 6 -7 0\n5 0\n7 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) | (xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 2\n", "1 2 -5 0\n3 4 5 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) & (!xp1 | v[4].clone())).index
            },
            concat!(
                "p cnf 7 7\n",
                "-1 6 0\n-2 6 0\n1 2 -6 0\n3 -5 6 0\n4 -6 -7 0\n5 0\n7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) | (!xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 4\n", "-1 5 0\n-2 5 0\n1 2 -5 0\n1 -1 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((!xp1.clone() | v[3].clone()) | (xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 4\n", "-1 5 0\n-2 5 0\n1 2 -5 0\n1 -1 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 7 7\n",
                "1 -6 0\n2 -6 0\n-5 6 0\n3 -5 0\n6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) & (xp1 & v[4].clone())).index
            },
            concat!("p cnf 5 6\n", "1 -5 0\n2 -5 0\n5 0\n3 0\n5 0\n4 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 7 8\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) & (!xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 5 7\n",
                "1 -5 0\n2 -5 0\n-1 -2 5 0\n5 0\n3 0\n-5 0\n4 0\n"
            )
        );

        expr_creator_testcase!(
            ec,
            v,
            5,
            {
                let xp1 = (v[1].clone() | v[5].clone()).imp(v[2].clone());
                ((xp1.clone() | v[3].clone()) & (!xp1 | v[4].clone())).index
            },
            concat!(
                "p cnf 9 10\n",
                "-1 8 0\n-5 8 0\n1 5 -8 0\n7 8 0\n-2 7 0\n2 -7 -8 0\n",
                "3 -6 7 0\n4 -7 -9 0\n6 0\n9 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_complex() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = !v[1].clone() & v[2].clone();
                (xp1.clone() | !v[3].clone() ^ (v[1].clone() | v[2].clone())).index
            },
            concat!(
                "p cnf 6 8\n",
                "-1 -4 0\n2 -4 0\n-1 6 0\n-2 6 0\n1 2 -6 0\n-3 -5 6 0\n3 -5 -6 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            {
                let xp1 = v[1].clone().imp(v[2].clone());
                let xp2 = v[3].clone().imp(v[2].clone());
                let xp3 = (xp1.clone() ^ xp2.clone()) | v[4].clone();
                let xp4 = (xp1.clone().bequal(xp2.clone())) & v[5].clone();
                let xp5 = (xp1.clone() | xp3.clone()) & (xp2.clone() | xp4.clone());
                let xp6 = (xp1.clone() & !xp3.clone()) | (!xp2.clone() & xp4.clone());
                (xp6.clone().imp(xp5.clone())).index
            },
            concat!(
                "p cnf 17 25\n",
                "1 8 0\n-2 8 0\n-1 2 -8 0\n3 11 0\n-2 11 0\n2 -3 -11 0\n8 -10 11 0\n",
                "-8 -10 -11 0\n4 -9 10 0\n7 -8 9 0\n8 -11 -14 0\n-8 11 -14 0\n8 11 14 0\n",
                "-8 -11 14 0\n-13 14 0\n5 -13 0\n-5 13 -14 0\n11 12 -13 0\n6 -7 0\n",
                "6 -12 0\n8 9 -16 0\n11 13 -17 0\n-15 16 0\n-15 17 0\n-6 15 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            9,
            {
                let c1 =
                    ((v[2].clone() ^ v[3].clone()) & v[1].clone()) | (v[2].clone() & v[3].clone());
                let c2 = ((v[4].clone() ^ v[5].clone()) & c1) | (v[4].clone() & v[5].clone());
                let c3 = ((v[6].clone() ^ v[7].clone()) & c2) | (v[6].clone() & v[7].clone());
                (((v[8].clone() ^ v[9].clone()) & c3) | (v[8].clone() & v[9].clone())).index
            },
            concat!(
                "p cnf 24 28\n",
                "8 9 -11 0\n-8 -9 -11 0\n6 7 -14 0\n-6 -7 -14 0\n4 5 -17 0\n-4 -5 -17 0\n",
                "2 3 -20 0\n-2 -3 -20 0\n-19 20 0\n1 -19 0\n2 -21 0\n3 -21 0\n-18 19 21 0\n",
                "-16 17 0\n-16 18 0\n4 -22 0\n5 -22 0\n-15 16 22 0\n-13 14 0\n-13 15 0\n",
                "6 -23 0\n7 -23 0\n-12 13 23 0\n-10 11 0\n-10 12 0\n8 -24 0\n9 -24 0\n10 24 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            9,
            {
                let c1 =
                    ((v[2].clone() ^ v[3].clone()) & v[1].clone()) | (v[2].clone() & v[3].clone());
                let c2 = ((v[4].clone() ^ v[5].clone()) & c1) | (v[4].clone() & v[5].clone());
                let c3 =
                    ((v[6].clone() ^ v[7].clone()) & c2.clone()) | (v[6].clone() & v[7].clone());
                let c4 = ((v[8].clone() ^ v[9].clone()) & c3) | (v[8].clone() & v[9].clone());
                (c2.imp(c4)).index
            },
            concat!(
                "p cnf 24 40\n",
                "4 5 -12 0\n-4 -5 -12 0\n4 -5 12 0\n-4 5 12 0\n2 3 -15 0\n-2 -3 -15 0\n",
                "2 -3 15 0\n-2 3 15 0\n-14 15 0\n1 -14 0\n-1 14 -15 0\n2 -16 0\n3 -16 0\n",
                "-2 -3 16 0\n13 -14 0\n13 -16 0\n-13 14 16 0\n-11 12 0\n-11 13 0\n",
                "11 -12 -13 0\n4 -17 0\n5 -17 0\n-4 -5 17 0\n10 -11 0\n10 -17 0\n-10 11 17 0\n",
                "8 9 -19 0\n-8 -9 -19 0\n6 7 -22 0\n-6 -7 -22 0\n-21 22 0\n10 -21 0\n6 -23 0\n",
                "7 -23 0\n-20 21 23 0\n-18 19 0\n-18 20 0\n8 -24 0\n9 -24 0\n-10 18 24 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_quantsets() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            [(Quantifier::Exists, [1]), (Quantifier::ForAll, [2])],
            concat!(
                "p cnf 7 8\n",
                "e 1 0\na 2 0\ne 5 6 7 0\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            [
                (Quantifier::Exists, [1]),
                (Quantifier::ForAll, [2]),
                (Quantifier::Exists, [3])
            ],
            concat!(
                "p cnf 7 8\n",
                "e 1 0\na 2 0\ne 3 5 6 7 0\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() & v[2].clone()).index },
            [(Quantifier::Exists, [1]), (Quantifier::ForAll, [2])],
            concat!("p cnf 2 2\n", "e 1 0\na 2 0\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            [(Quantifier::Exists, [1, 2]), (Quantifier::ForAll, [3, 4])],
            concat!(
                "p cnf 7 4\n",
                "e 1 2 0\na 3 4 0\ne 6 7 0\n",
                "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            [(Quantifier::ForAll, [1, 2]), (Quantifier::Exists, [3, 4])],
            concat!(
                "p cnf 7 4\n",
                "a 1 2 0\ne 3 4 6 7 0\n",
                "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n"
            )
        );
    }

    use generic_array::typenum::*;

    #[test]
    fn test_expr_creator_intexprs() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // single operator testcases
        expr_creator_testcase!(
            ec,
            v,
            12,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (x1.equal(x2)).index
            },
            concat!(
                "p cnf 18 18\n",
                "1 -7 -13 0\n-1 7 -13 0\n2 -8 -14 0\n-2 8 -14 0\n3 -9 -15 0\n-3 9 -15 0\n",
                "4 -10 -16 0\n-4 10 -16 0\n5 -11 -17 0\n-5 11 -17 0\n6 -12 -18 0\n-6 12 -18 0\n",
                "13 0\n14 0\n15 0\n16 0\n17 0\n18 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            12,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (x1.less_than(x2)).index
            },
            concat!(
                "p cnf 31 36\n",
                "6 -12 -14 0\n-6 12 -14 0\n5 -11 -17 0\n-5 11 -17 0\n4 -10 -20 0\n-4 10 -20 0\n",
                "3 -9 -23 0\n-3 9 -23 0\n2 -8 -26 0\n-2 8 -26 0\n-25 26 0\n-1 -25 0\n7 -25 0\n",
                "-2 -27 0\n8 -27 0\n-24 25 27 0\n-22 23 0\n-22 24 0\n-3 -28 0\n9 -28 0\n",
                "-21 22 28 0\n-19 20 0\n-19 21 0\n-4 -29 0\n10 -29 0\n-18 19 29 0\n-16 17 0\n",
                "-16 18 0\n-5 -30 0\n11 -30 0\n-15 16 30 0\n-13 14 0\n-13 15 0\n-6 -31 0\n",
                "12 -31 0\n13 31 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            13,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (!x1.less_than(x2) ^ v[13].clone()).index
            },
            concat!(
                "p cnf 33 68\n6 -12 -16 0\n-6 12 -16 0\n6 12 16 0\n-6 -12 16 0\n5 -11 -19 0\n",
                "-5 11 -19 0\n5 11 19 0\n-5 -11 19 0\n4 -10 -22 0\n-4 10 -22 0\n4 10 22 0\n",
                "-4 -10 22 0\n3 -9 -25 0\n-3 9 -25 0\n3 9 25 0\n-3 -9 25 0\n2 -8 -28 0\n",
                "-2 8 -28 0\n2 8 28 0\n-2 -8 28 0\n-27 28 0\n-1 -27 0\n7 -27 0\n1 -7 27 -28 0\n",
                "-2 -29 0\n8 -29 0\n2 -8 29 0\n26 -27 0\n26 -29 0\n-26 27 29 0\n-24 25 0\n",
                "-24 26 0\n24 -25 -26 0\n-3 -30 0\n9 -30 0\n3 -9 30 0\n23 -24 0\n23 -30 0\n",
                "-23 24 30 0\n-21 22 0\n-21 23 0\n21 -22 -23 0\n-4 -31 0\n10 -31 0\n4 -10 31 0\n",
                "20 -21 0\n20 -31 0\n-20 21 31 0\n-18 19 0\n-18 20 0\n18 -19 -20 0\n-5 -32 0\n",
                "11 -32 0\n5 -11 32 0\n17 -18 0\n17 -32 0\n-17 18 32 0\n-15 16 0\n-15 17 0\n",
                "15 -16 -17 0\n-6 -33 0\n12 -33 0\n6 -12 33 0\n14 -15 0\n14 -33 0\n-14 15 33 0\n",
                "13 -14 0\n-13 14 0\n"
            )
        );
    }
}
