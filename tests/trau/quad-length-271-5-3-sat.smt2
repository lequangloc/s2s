( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  z3 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat z1  t1  )  z2  )  ) ( Concat t3  z3  )  ) ( Concat( Concat( Concat( Concat x2  "dcab"  )  x1  ) ( Concat( Concat z2  t2  )  z1  )  ) ( Concat z3  "nm"  )  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( assert ( >( Length z2  )  32000  ) )
 ( check-sat )
 