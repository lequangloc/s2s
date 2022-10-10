( declare-fun  x () String )
 ( declare-fun  y () String )
 ( declare-fun  i () Int )
 ( assert ( =( Concat "ab"  x  ) ( Concat x  "ba"  )  ) )
 ( assert ( =( Concat "c"  y  ) ( Concat y  "c"  )  ) )
 ( assert ( exists ( ( i Int )  ) ( =( Length x  ) ( +( * 4  i  )  3  )  ) ) )
 ( assert ( =( Length x  ) ( * 2 ( Length y  )  )  ) )
 ( check-sat )
 