( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dcb"  )  x2  ) ( Concat t2 ( Concat( Concat z2 ( Concat "abf"  z1  )  )  t1  )  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat t3 ( Concat( Concat z1 ( Concat "fba"  z2  )  )  t4  )  )  )  ) )
 ( check-sat )
 