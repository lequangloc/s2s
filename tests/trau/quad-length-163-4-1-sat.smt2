( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dcb"  )  x2  ) ( Concat( Concat z2 ( Concat "abf"  z1  )  )  t1  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat( Concat z1 ( Concat "fba"  z2  )  )  "a"  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( check-sat )
 