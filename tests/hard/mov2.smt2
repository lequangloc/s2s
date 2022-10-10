(set-logic QF_S)

( declare-fun  x () String )
 ( declare-fun  y () String )
( declare-fun  i () Int )
 ( assert ( =( str.++( str.++ x  "ab"  )  y  ) ( str.++( str.++ y  "ba"  )  x  )  ) )
 ( assert ( > i   0  ) )
 ( assert ( =( str.len y  ) (+ (* 2 i) 1)  ) )
( assert ( =( str.len x  ) (+ (str.len y) 2)  ) )
 ( check-sat )
 
