( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  z3 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( declare-fun  t5 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat z1  "ab"  )  z2  )  ) ( Concat( Concat t5  t1  )  z3  )  ) ( Concat( Concat( Concat( Concat x2  "dcvb"  )  x1  ) ( Concat( Concat z2 ( Concat t4  t2  )  )  z1  )  ) ( Concat z3 ( Concat t3  "ab"  )  )  )  ) )
 ( check-sat )
 