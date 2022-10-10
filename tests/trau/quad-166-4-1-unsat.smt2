( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( Concat( Concat( Concat x1  "dvb"  )  x2  ) ( Concat t1 ( Concat z2 ( Concat "abf"  z1  )  )  )  ) ( Concat( Concat( Concat x2  "bcd"  )  x1  ) ( Concat "bc" ( Concat z1 ( Concat "fba"  z2  )  )  )  )  ) )
 ( check-sat )
 