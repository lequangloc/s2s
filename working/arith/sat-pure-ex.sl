

pred Q<x,y> == P1(x) * P2(y).

pred P1<x> == x=0
  or exists x1: P1(x1) & x=x1+2.

pred P2<y> == y=0
  or exists y1: P2(y1) & y=y1+3.


//checksat[unsat] (exists k: Q(x,y) & x = 2k+1).

checksat[unsat] (exists k : P1(x) & x = 2*k +1).

checksat[unsat] Q(x, y) & x = 2*y +1.
/*
(declare-var x Int)
(declare-var y Int)
(declare-rel Q (Int Int))

(declare-rel P1 (Int))

(declare-rel P2 (Int))

(rule (=> (and (P2 y) (and (P1 x) true)) (Q x y)))

(rule (=> (= x 0) (P1 x)))

(rule (=> (P1 (- x 2))  (P1 x)))

(rule (=> (= y 0) (P2 y)))

(rule (=> (P2 (- y 3)) (P2 y)))

(declare-rel Q_39 (Int Int))

(rule (=> (and (Q x y) (= x (+ 1 (* 2 y))))(Q_39 x y)))

(query Q_39 )

*/