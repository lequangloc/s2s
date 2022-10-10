ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int data;
}.

pred sdll<E:RefDll_t,P:RefDll_t,dt1:int,F:RefDll_t,L:RefDll_t,dt2:int> ==
 emp & E = F & P = L & dt1 = dt2
or (exists u,dt3: E::RefDll_t<next = u,prev = P,data = dt1> * sdll(u,E,dt3,F,L,dt2) & dt1 > dt3+1).

/*
checkent[valid]  emp & true
         |- exists x5: sdll(E3,F3,x5,E3,F3,x3).
*/

/*
checkent[valid]  sdll(E5,F5,y5,E3,F3,x3)
         |- exists x5: sdll(E5,F5,x5,E3,F3,x3).
*/

/*
checkent[valid]  sdll(E5,F5,y5,E3,F3,x3)
         |-  sdll(E5,F5,y5,E3,F3,x3).
*/


checkent[valid]  sdll(E1,F1,x1,E2,F2,x2) * sdll(E2,F2,x2,E3,F3,x3)
         |- sdll(E1,F1,x1,E3,F3,x3).


/*
checkent[valid]  sdll(E1,F1,x1,E2,F2,y2) * sdll(E2,F2,x2,E3,F3,x3)
         |- sdll(E1,F1,x1,E3,F3,x3).
*/

/*
checkent[valid]  sdll(E1,F1,x1,E2,F2,y2) * sdll(E2,F2,x2,E3,F3,x3) & y2<x2
         |- sdll(E1,F1,x1,E3,F3,x3).

*/