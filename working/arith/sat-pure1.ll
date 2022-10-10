// the singleton heap predicate which models a data structure
data node {
    node next;
    node prev;
}.


pred Q<x,y> == P1(x) * P2(y).

/*
pred Q< x,y> == P1(x)_0^0 * P2(y)_0^1 & true
 inv exists idx_27: 0=idx_27 && y>=0 && x>=0.

*/

pred P1<x> == x=0
  or exists x1: P1(x1) & x=x1+2.

pred P2<y> == y=0
  or exists y1: P2(y1) & y=y1+3.


checksat[sat] P1(x).

/*

(declare-var x Int)
(declare-var x1_28 Int)

(declare-rel P1 (Int))
(rule (=> (= x 0) (P1 x)))

(rule (=>  (and (= x1_28 (- x 2)) (P1 x1_28)) (P1 x) ))

(declare-rel Q_29 (Int))

(rule (=> (and (P1 x) true) (Q_29 x)))

(query Q_29 )

sat
===================

(set-option :fixedpoint.engine datalog)
(declare-fun x () Int)
(declare-fun x1_28 () Int)
(declare-rel P1 (Int))

(rule (P1 0))

(rule (=> (P1 (- x 2)) (P1 x)))

(declare-rel Q_29 (Int))

(rule (=> (P1 x) (Q_29 x)))

(query Q_29 )

(error "query failed: Uninterpreted 'x' in <null>:
P1(#0) :- 
 P1(#1),
 (= (:var 1) (- x 2)),
 (= (:var 0) x).
")
unknown



*/