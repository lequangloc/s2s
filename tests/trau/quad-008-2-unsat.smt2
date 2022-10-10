( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( Concat( Concat( Concat x312  "abbc"  )  x429  )  "abx"  ) ( Concat( Concat( Concat x429  "cbca"  )  x312  )  "abx"  )  ) )
 ( check-sat )
 