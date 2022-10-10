( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dcb"  )  x2  ) ( Concat( Concat z2 ( Concat "abcf"  z1  )  ) ( Concat t1  t2  )  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat( Concat z1 ( Concat "fbac"  z2  )  )  "x"  )  )  ) )
 ( check-sat )
 