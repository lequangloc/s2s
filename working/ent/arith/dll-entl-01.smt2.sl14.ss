
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int data;
}.

pred sdll<E:RefDll_t,P:RefDll_t,dt1:int,F:RefDll_t,L:RefDll_t,dt2:int> ==
 emp & E = F & P = L & dt1 = dt2
or (exists u,dt3: E::RefDll_t<next = u,prev = P,data = dt1> * sdll(u,E,dt3,F,L,dt2) & dt1 < dt3+1).


                                                                  /*
checkent[valid] sdll(E1,F1,x1,E3,F3,x3) * sdll(E2,F2,x2,E4,F4,x4) * sdll(E3,F3,x3,E4,F4,x4) * sdll(E4,F4,y4,E3,F3,y3) * sdll(E3,F3,x3,E5,F5,x5) * sdll(E5,F5,y5,E3,F3,y3) * sdll(E4,F4,x5,E6,F6,x6) & x4 = x5 & x4 = y4 & x3 = y3 & x5 = y5
         |- sdll(E1,F1,x1,E3,F3,x3) * sdll(E2,F2,x2,E6,F6,x6).
                                                                  */

                                                                  //checksat sdll(E3,F3,x3,E4,F4,x4) * sdll(E4,F4,x4,E3,F3,x3) * sdll(E3,F3,x3,E5,F5,x5) * sdll(E5,F5,x5,E3,F3,x3) & E3 != E4.

                                                                  /*
checkent[valid]  sdll(E3,F3,x3,E4,F4,x4) |- sdll(E3,F3,x3,E4,F4,x4).
                                                                  */

                                                                  /*
checkent[valid]  sdll(E3,F3,x3,E4,F4,x4) * sdll(E4,F4,y4,E3,F3,y3) * sdll(E3,F3,x3,E5,F5,x5) * sdll(E5,F5,y5,E3,F3,y3) & x4 = x5 & x4 = y4 & x3 = y3 & x5 = y5
         |- sdll(E3,F3,x3,E3,F3,x3) .
                                                                  */

checksat[unsat]  E3::RefDll_t<u,F3,dt1> * sdll(u,E3,x33,E4,F4,x4) * sdll(E4,F4,y4,E3,F3,y3) * sdll(E3,F3,x3,E5,F5,x5) * sdll(E5,F5,y5,E3,F3,y3) & x4 = x5 & x4 = y4 & x3 = y3 & x5 = y5 & x3<x33+1.

                                                                  /*
checksat[unsat]  E3::RefDll_t<u,F3,dt1> * sdll(u,E3,x33,E4,F4,x4) * sdll(E4,F4,x4,E3,F3,x3) * sdll(E3,F3,x3,E5,F5,x5) * sdll(E5,F5,x5,E3,F3,x3) & x3<x33+1.
                                                                  */

