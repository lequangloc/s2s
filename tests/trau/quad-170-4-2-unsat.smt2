( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dcl"  )  x2  ) ( Concat( Concat t1 ( Concat z2 ( Concat "abf"  z1  )  )  )  t2  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat( Concat "a" ( Concat z1 ( Concat "fba"  z2  )  )  )  "x"  )  )  ) )
 ( check-sat )
 