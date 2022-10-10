( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( Concat "abx" ( Concat( Concat x312  "abbc"  )  x429  )  ) ( Concat "abx" ( Concat( Concat x429  "cbca"  )  x312  )  )  ) )
 ( check-sat )
 