ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int data;
}.

pred sdll<E:RefDll_t,P:RefDll_t,dt1:int,F:RefDll_t,L:RefDll_t,dt2:int> ==
 emp & E = F & P = L & dt1 = dt2
or (exists u,dt3: E::RefDll_t<next = u,prev = P,data = dt1> * sdll(u,E,dt3,F,L,dt2) & dt1 < dt3+1).

                                                                  /*
pred sdll<E:RefDll_t,P:RefDll_t,dt1:int,F:RefDll_t,L:RefDll_t,dt2:int> ==
 emp & E = F & P = L & dt1 = dt2
or (exists u,dt3: E::RefDll_t<next = u,prev = P,data = dt1> * sdll(u,E,dt3,F,L,dt2) & dt1 > dt3+1).

                                                                  */


