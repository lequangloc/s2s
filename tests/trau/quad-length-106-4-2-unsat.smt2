( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z1  )  "a"  ) ( Concat( Concat( Concat x1  "abdc"  )  x2  )  t1  )  ) ( Concat "cd"  z2  )  ) ( Concat( Concat( Concat( Concat z1  "aa"  )  t2  ) ( Concat( Concat( Concat x2  "dsba"  )  x1  )  "av"  )  ) ( Concat z2  "cc"  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 