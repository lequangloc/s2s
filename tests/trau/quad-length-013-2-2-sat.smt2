( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat( Concat x7  "abbc"  )  x8  )  z  ) ( Concat( Concat( Concat( Concat x8  "cbba"  )  x7  )  "ab"  )  t  )  ) )
 ( assert ( >( Length x7  )  32000  ) )
 ( check-sat )
 