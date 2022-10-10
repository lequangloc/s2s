
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred ldll<E:RefDll_t,P:RefDll_t,len1:int,F:RefDll_t,L:RefDll_t,len2:int> ==
 emp & E = F & P = L & len1 = len2
or (exists u,len3: E::RefDll_t<next = u,prev = P> * ldll(u,E,len3,F,L,len2) & len1 = len3+1).

checkent[invalid] ldll(E1,E1_prime,x1,E3,E3_prime,x3) * ldll(E2,E2_prime,x2,E4,E4_prime,x4) * ldll(E3,E3_prime,x3,E4,E7,x4) * ldll(E4,E4_prime,x4_prime,E3,E8,x3_prime) * ldll(E3,E3_prime,x3,E5,E5_prime,x5) * ldll(E5,E5_prime,x5_prime,E3,E9,x3_prime) * ldll(E4,E4_prime,x4,E6,E6_prime,x6)
         |- ldll(E1,E1_prime,x1,E3,E3_prime,x3) * ldll(E2,E2_prime,x2,E6,E6_prime,x6).

