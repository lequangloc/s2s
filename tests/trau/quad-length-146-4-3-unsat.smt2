( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat "cb"  z1  ) ( Concat t1  t3  )  )  ) ( Concat "cd"  z2  )  ) ( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  ) ( Concat( Concat z1  "ba"  )  t2  )  ) ( Concat z2  "dc"  )  )  ) )
 ( check-sat )
 