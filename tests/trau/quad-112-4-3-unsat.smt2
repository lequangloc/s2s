( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "gh"  z1  )  "a"  ) ( Concat( Concat( Concat x1  "abdc"  )  x2  )  t1  )  ) ( Concat( Concat "cd"  z2  )  t3  )  ) ( Concat( Concat( Concat( Concat z1  "ba"  )  t2  ) ( Concat( Concat( Concat x2  "dcca"  )  x1  )  "xx"  )  ) ( Concat( Concat z2  "dc"  )  "gh"  )  )  ) )
 ( check-sat )
 