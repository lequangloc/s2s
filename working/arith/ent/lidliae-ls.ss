
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred ldll<E:RefDll_t,P:RefDll_t,len1:int,F:RefDll_t,L:RefDll_t,len2:int> ==
 emp & E = F & P = L & len1 = len2
or (exists u,len3: E::RefDll_t<next = u,prev = P> * ldll(u,E,len3,F,L,len2) & len1 = len3+1).


                                                                    
checkent[valid] E1::RefDll_t<next = E2,prev = E1_p> * ldll(E2,E2_p,x2,E3,E3_p,x3) & E1 = E2_p & x1 = x2+1
         |- ldll(E1,E1_p,x1,E3,E3_p,x3).
                                                                             
                                                                    /*
  checkent[unsat] (exists len3_30,len3_33,idx_31,idx_19,idx_34: E2::RefDll_t<E3_p,E2_p> * E3_p::RefDll_t<E3,E2> * E2_p::RefDll_t<E2,E1_p> & E2!=E3_p & E2!=null & E3_p!=null & x2=(idx_19+x3) & x2>=x3 & len3_30=(idx_31+x3) & len3_30>=x3 & len3_33=(idx_34+x3) & len3_33>=x3 & x2=(1+len3_30) & len3_30=(1+len3_33) & x1=(1+x2))
    |- ldll(E2_p,E1_p,x1,E3,E3_p,x3).
*/
                                                                    /*                                                                    
 checkent[valid] (exists len3_30,len3_33: E2::RefDll_t<E3_p,E2_p> * E3_p::RefDll_t<E3,E2> * E2_p::RefDll_t<E2,E1_p> & E2!=E3_p & E2!=null & E3_p!=null &  x2>=x3 & len3_30>=x3  & len3_33>=x3 & x2=(1+len3_30) & len3_30=(1+len3_33) & x1=(1+x2))
 |- ldll(E2_p,E1_p,x1,E3,E3_p,x3). */
                                                               /*
E1::RefDll_t<u,E1_p> * ldll(u,E1,len3,E3,E3_p,x3) & x1 = len3+1
E1::RefDll_t<E3,E1_p> & E1=E3_p & x1=x3+1
                                                                     */
                                                                    /*
checkent[invalid] ldll(E1,E1_prime,x1,E3,E3_prime,x3) * ldll(E2,E2_prime,x2,E4,E4_prime,x4) * ldll(E3,E3_prime,x3,E4,E4_prime,x4) * ldll(E4,E4_prime,x4_prime,E3,E3_prime,x3_prime) * ldll(E3,E3_prime,x3,E5,E5_prime,x5) * ldll(E5,E5_prime,x5_prime,E3,E3_prime,x3_prime) * ldll(E4,E4_prime,x4,E6,E6_prime,x6) & E2 = E4 & E3 = E5
         |- ldll(E1,E1_prime,x1,E6,E6_prime,x6).
                                                                    */
