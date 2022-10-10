ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int data;
}.

pred lsdll<E:RefDll_t,P:RefDll_t,dt1:int,len1:int,F:RefDll_t,L:RefDll_t,dt2:int,len2:int> ==
 emp & E = F & P = L & dt1 = dt2 & len1 = len2
or (exists u,dt3,len3: E::RefDll_t<next = u,prev = P,data = dt1> * lsdll(u,E,dt3,len3,F,L,dt2,len2) & dt1 > dt3+1 & len1 = len3+1).

