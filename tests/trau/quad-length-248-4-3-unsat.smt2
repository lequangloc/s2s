( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  y1 () String )
 ( declare-fun  y2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abec"  )  x2  ) ( Concat( Concat z1  t3  )  z2  )  ) ( Concat( Concat y1  t2  )  y2  )  ) ( Concat( Concat( Concat( Concat x2  "dcab"  )  x1  ) ( Concat( Concat z2  t1  )  z1  )  ) ( Concat( Concat y2  "av"  )  y1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 