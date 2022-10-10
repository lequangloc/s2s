( declare-fun  x () String )
 ( assert ( =( Concat( Concat "c"  "b"  )  x  ) ( Concat( Concat x  "c"  )  "c"  )  ) )
 ( assert ( >( Length x  )  32000  ) )
 ( check-sat )
 