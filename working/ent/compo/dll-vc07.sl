
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred ldll<E:RefDll_t,P:RefDll_t,len1:int,F:RefDll_t,L:RefDll_t,len2:int> ==
 emp & E = F & P = L & len1 = len2
or (exists u,len3: E::RefDll_t<next = u,prev = P> * ldll(u,E,len3,F,L,len2) & len1 = len3+1).

checkent[valid] E1::RefDll_t<next = E2,prev = E1_p> * ldll(E2,E2_p,x2,E3,E3_p,x3) & E1 = E2_p & x1 = x2+1
         |- ldll(E1,E1_p,x1,E3,E3_p,x3).

