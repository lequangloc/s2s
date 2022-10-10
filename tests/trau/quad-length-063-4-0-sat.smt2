( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z1  ) ( Concat "fe"  z2  )  ) ( Concat x1  "abfe"  )  )  x2  ) ( Concat( Concat( Concat z1  "ba"  ) ( Concat z2  "ef"  )  ) ( Concat( Concat x2  "feba"  )  x1  )  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( check-sat )
 