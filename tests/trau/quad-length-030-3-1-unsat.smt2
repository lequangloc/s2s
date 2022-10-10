( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat x1 ( Concat t  t  )  )  x2  ) ( Concat( Concat x2  "b"  )  x1  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 