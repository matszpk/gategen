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

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::Write;
use std::ops::Neg;
use std::rc::Rc;

use crate::gate::{Literal, VarLit};

use gatesim::{Circuit, Gate};

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

    pub fn to_circuit(
        &self,
        outputs: impl IntoIterator<Item = usize>,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        type Unsigned<T> = <T as VarLit>::Unsigned;
        let mut input_map = HashMap::new();
        let outputs = Vec::from_iter(outputs);
        #[derive(Clone, Copy)]
        struct SimpleEntry {
            node_index: usize,
            path: usize,
        }
        impl SimpleEntry {
            #[inline]
            fn new_root(start: usize) -> Self {
                Self {
                    node_index: start,
                    path: 0,
                }
            }
        }
        let mut visited = vec![false; self.nodes.len()];
        // collect inputs
        for start in &outputs {
            let mut stack = vec![SimpleEntry::new_root(*start)];
            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();
                if !first_path || !visited[node_index] {
                    if !node.is_unary() && first_path {
                        visited[node_index] = true;
                    }
                    match node {
                        Node::Single(l) => {
                            if let Some(l) = l.varlit() {
                                input_map.insert(
                                    l.positive().unwrap(),
                                    Unsigned::<T>::try_from(input_map.len()).unwrap(),
                                );
                            } else {
                                panic!("Unsupported!");
                            }
                        }
                        _ => {}
                    }
                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry {
                            node_index: node.first_path(),
                            path: 0,
                        });
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry {
                            node_index: node.second_path(),
                            path: 0,
                        });
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop();
                }
            }
        }

        // create circuit
        let mut visited = vec![false; self.nodes.len()];
        let mut gate_output_map = HashMap::<usize, (Unsigned<T>, bool)>::new();
        let input_len = input_map.len();
        let mut gates = vec![];
        let mut circ_outputs = vec![];
        for start in &outputs {
            let mut stack = vec![SimpleEntry::new_root(*start)];
            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();

                let mut new_node = || {
                    match node {
                        Node::Single(l) => {
                            let l = l.varlit().unwrap();
                            let lit = input_map[&l.positive().unwrap()];
                            gate_output_map.insert(node_index, (lit, !l.is_positive()));
                        }
                        Node::Negated(fidx) => {
                            let (gi, n) = gate_output_map.get(&fidx).unwrap();
                            gate_output_map.insert(node_index, (*gi, !n));
                        }
                        Node::And(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    // and(!gi1,!gi2) -> nor(gi1,gi2)
                                    (Gate::new_nor(*gi1, *gi2), false)
                                } else {
                                    (Gate::new_nimpl(*gi2, *gi1), false)
                                }
                            } else if *n2 {
                                (Gate::new_nimpl(*gi1, *gi2), false)
                            } else {
                                (Gate::new_and(*gi1, *gi2), false)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Or(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    (Gate::new_and(*gi1, *gi2), true)
                                } else {
                                    (Gate::new_nimpl(*gi1, *gi2), true)
                                }
                            } else if *n2 {
                                (Gate::new_nimpl(*gi2, *gi1), true)
                            } else {
                                (Gate::new_nor(*gi1, *gi2), true)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Xor(fidx, sidx) | Node::Equal(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let neg = matches!(node, Node::Equal(_, _));
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    // and(!gi1,!gi2) -> nor(gi1,gi2)
                                    (Gate::new_xor(*gi1, *gi2), neg)
                                } else {
                                    (Gate::new_xor(*gi1, *gi2), !neg)
                                }
                            } else if *n2 {
                                (Gate::new_xor(*gi1, *gi2), !neg)
                            } else {
                                (Gate::new_xor(*gi1, *gi2), neg)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Impl(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    (Gate::new_nimpl(*gi2, *gi1), true)
                                } else {
                                    (Gate::new_nor(*gi1, *gi2), true)
                                }
                            } else if *n2 {
                                (Gate::new_and(*gi1, *gi2), true)
                            } else {
                                (Gate::new_nimpl(*gi1, *gi2), true)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                    };
                };

                if !first_path || !visited[node_index] {
                    if !node.is_unary() && first_path {
                        visited[node_index] = true;
                    }
                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry {
                            node_index: node.first_path(),
                            path: 0,
                        });
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry {
                            node_index: node.second_path(),
                            path: 0,
                        });
                    } else {
                        new_node();
                        stack.pop();
                        if stack.is_empty() {
                            circ_outputs.push(gate_output_map[&node_index]);
                        }
                    }
                } else {
                    if !visited[node_index] {
                        new_node();
                    }
                    stack.pop();
                    if stack.is_empty() {
                        circ_outputs.push(gate_output_map[&node_index]);
                    }
                }
            }
        }
        (
            Circuit::<<T as VarLit>::Unsigned>::new(
                Unsigned::<T>::try_from(input_len).unwrap(),
                gates,
                circ_outputs,
            )
            .unwrap(),
            input_map,
        )
    }
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
        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $res: expr) => {
            $ec = ExprCreator::<isize>::new();
            $v.clear();
            $v.push(BoolExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(BoolExprNode::variable($ec.clone()));
            }
            let expr_indices = $expr;
            test_println!("expr: {:?}", expr_indices);
            assert_eq!($res, $ec.borrow().to_circuit(expr_indices));
        };
    }

    #[test]
    fn test_to_circuit_1() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [v[1].index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [(!v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, true)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [(v[1].clone() & v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        for (func_name, aneg, bneg, rneg, expected) in [
            (
                "and",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
        ] {
            expr_creator_testcase!(
                ec,
                v,
                2,
                {
                    let a = if aneg { !v[1].clone() } else { v[1].clone() };
                    let b = if bneg { !v[2].clone() } else { v[2].clone() };
                    let r = match func_name {
                        "and" => a.clone() & b.clone(),
                        "or" => a.clone() | b.clone(),
                        "xor" => a.clone() ^ b.clone(),
                        "impl" => a.clone().imp(b.clone()),
                        "eq" => a.clone().bequal(b.clone()),
                        _ => {
                            panic!("Unsupported");
                        }
                    };
                    if rneg {
                        [(!r).index]
                    } else {
                        [r.index]
                    }
                },
                expected
            );
        }
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & v[2].clone() & v[3].clone()).index] },
            (
                Circuit::new(3, [Gate::new_and(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & (v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [((v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & !(v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_and(3, 2)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!(v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_and(3, 2)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() & (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_xor(0, 1), Gate::new_nor(3, 2)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() | (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_xor(0, 1), Gate::new_and(3, 2)],
                    [(4, true)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
    }
}
