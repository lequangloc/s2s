( declare-fun  x3 () String )
 ( declare-fun  x4 () String )
 ( assert ( =( Concat( Concat x3  "aabc"  )  x4  ) ( Concat( Concat x4  "bbaa"  )  x3  )  ) )
 ( check-sat )
 