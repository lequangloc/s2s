( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( assert ( =( Concat( Concat( Concat "ab"  z1  ) ( Concat( Concat x1  "abdc"  )  x2  )  ) ( Concat( Concat "cd"  z2  ) ( Concat t4  t3  )  )  ) ( Concat( Concat( Concat z1  "ba"  ) ( Concat( Concat x2  "ddba"  )  x1  )  ) ( Concat( Concat z2  "cc"  ) ( Concat t1  t2  )  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 