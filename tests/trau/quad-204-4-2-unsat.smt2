( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dcb"  )  x2  ) ( Concat z2 ( Concat( Concat t2  t1  )  z1  )  )  ) ( Concat( Concat( Concat x2  "bce"  )  x1  ) ( Concat z1 ( Concat "abc"  z2  )  )  )  ) )
 ( check-sat )
 