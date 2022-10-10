( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat( Concat x7  "abbcd"  )  x8  )  z  ) ( Concat( Concat( Concat( Concat x8  "cbbaa"  )  x7  )  "ab"  )  t  )  ) )
 ( assert ( >( Length x7  )  16000  ) )
 ( assert ( =( Length x7  ) ( Length x8  )  ) )
 ( check-sat )
 