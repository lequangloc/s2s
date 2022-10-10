( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( Concat "axy" ( Concat( Concat x312  "abbc"  )  x429  )  ) ( Concat "axy" ( Concat( Concat x429  "cbba"  )  x312  )  )  ) )
 ( assert ( >( Length x312  )  16000  ) )
 ( check-sat )
 