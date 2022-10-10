
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred ldll<E:RefDll_t,P:RefDll_t,len1:int,F:RefDll_t,L:RefDll_t,len2:int> ==
 emp & E = F & P = L & len1 = len2
or (exists u,len3: E::RefDll_t<next = u,prev = P> * ldll(u,E,len3,F,L,len2) & len1 = len3+1).


checkent[valid] E1::RefDll_t<next = E2,prev = E1_p> * E2::RefDll_t<next = E3,prev = E2_p> * ldll(E3,E3_p,x3,E4,E4_p,x4) & E1 = E2_p & E2 = E3_p & x1 = x2+1 & x2 = x3+1
         |- ldll(E1,E1_p,x1,E3,E3_p,x3) * ldll(E3,E3_p,x3,E4,E4_p,x4) & x1 = x3+2.
