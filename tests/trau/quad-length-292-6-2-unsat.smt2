( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  y1 () String )
 ( declare-fun  y2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "atdc"  )  x2  ) ( Concat( Concat z1  t1  )  z2  )  ) ( Concat( Concat y1  "mn"  )  y2  )  ) ( Concat( Concat( Concat( Concat x2  "dcab"  )  x1  ) ( Concat( Concat z2  t2  )  z1  )  ) ( Concat( Concat y2  "nm"  )  y1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 