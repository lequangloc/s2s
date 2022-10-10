( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  x3 () String )
 ( assert ( =( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat x3  "ab"  )  ) ( Concat( Concat( Concat x2  "cdba"  )  x1  ) ( Concat "ba"  x3  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 