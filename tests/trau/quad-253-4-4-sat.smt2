( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  y1 () String )
 ( declare-fun  y2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat z1  "ef"  )  z2  )  ) ( Concat( Concat y1 ( Concat t1  t2  )  )  y2  )  ) ( Concat( Concat( Concat( Concat x2  "dcab"  )  x1  ) ( Concat( Concat z2  "fe"  )  z1  )  ) ( Concat( Concat y2 ( Concat t4  t3  )  )  y1  )  )  ) )
 ( check-sat )
 