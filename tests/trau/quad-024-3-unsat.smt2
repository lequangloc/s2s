( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  x3 () String )
 ( assert ( =( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat x3  "ab"  )  ) ( Concat( Concat( Concat x2  "cdba"  )  x1  ) ( Concat "ba"  x3  )  )  ) )
 ( check-sat )
 