( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat x1  "acb"  )  x2  ) ( Concat t2 ( Concat( Concat z2 ( Concat "abf"  z1  )  )  t1  )  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat t3 ( Concat z1 ( Concat "fba"  z2  )  )  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 