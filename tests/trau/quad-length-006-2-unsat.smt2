( declare-fun  x3 () String )
 ( declare-fun  x4 () String )
 ( assert ( =( Concat( Concat x3  "aabc"  )  x4  ) ( Concat( Concat x4  "bbaa"  )  x3  )  ) )
 ( assert ( >( Length x3  )  32000  ) )
 ( assert ( =( Length x4  ) ( Length x3  )  ) )
 ( check-sat )
 