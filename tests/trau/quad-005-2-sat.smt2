( declare-fun  x3 () String )
 ( declare-fun  x4 () String )
 ( assert ( =( Concat( Concat x3  "abbc"  )  x4  ) ( Concat( Concat x4  "cbba"  )  x3  )  ) )
 ( check-sat )
 