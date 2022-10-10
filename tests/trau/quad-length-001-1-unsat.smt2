( declare-fun  x () String )
 ( assert ( =( Concat( Concat "c"  x  )  "a"  ) ( Concat( Concat x  "a"  )  "a"  )  ) )
 ( assert ( >( Length x  )  3200  ) )
 ( check-sat )
 