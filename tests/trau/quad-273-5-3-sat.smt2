( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  z3 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat z1  "ef"  )  z2  )  ) ( Concat( Concat t1  t2  )  z3  )  ) ( Concat( Concat( Concat( Concat x2  "dcab"  )  x1  ) ( Concat( Concat z2  "fe"  )  z1  )  ) ( Concat z3  t3  )  )  ) )
 ( check-sat )
 