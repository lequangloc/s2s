( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( Concat( Concat( Concat x312  "abbc"  )  x429  )  "axy"  ) ( Concat( Concat( Concat x429  "cbba"  )  x312  )  "axy"  )  ) )
 ( check-sat )
 