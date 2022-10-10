( declare-fun  x () String )
 ( declare-fun  y () String )
 ( assert ( =( Concat( Concat "c"  "b"  )  x  ) ( Concat( Concat x  "c"  )  "c"  )  ) )
 ( assert ( =( Concat( Concat "a"  "d"  )  y  ) ( Concat( Concat y  "a"  )  "a"  )  ) )
 ( check-sat )
 