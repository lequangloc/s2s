(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  z3 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x1  "abde"  )  x2  ) ( str.++( str.++ z1  t1  )  z2  )  ) ( str.++ "mn"  z3  )  ) ( str.++( str.++( str.++( str.++ x2  "dcab"  )  x1  ) ( str.++( str.++ z2  t2  )  z1  )  ) ( str.++ z3  "nm"  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( =( str.len x1  ) ( str.len x2  )  ) )
 ( check-sat )
 