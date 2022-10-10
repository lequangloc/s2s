
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int data;
}.

pred lsdll<E:RefDll_t,P:RefDll_t,dt1:int,len1:int,F:RefDll_t,L:RefDll_t,dt2:int,len2:int> ==
 emp & E = F & P = L & dt1 = dt2 & len1 = len2
or (exists u,dt3,len3: E::RefDll_t<next = u,prev = P,data = dt1> * lsdll(u,E,dt3,len3,F,L,dt2,len2) & dt1 > dt3+1 & len1 = len3+1).


checkent[valid] lsdll(E1,F1,x1,u1,E3,F3,x3,u3) * lsdll(E2,F2,x2,u2,E4,F4,x4,u4) * lsdll(E3,F3,x3,u3,E4,F4,x4,u4) * lsdll(E4,F4,y4,u4,E3,F3,y3,u3) * lsdll(E3,F3,x3,u3,E5,F5,x5,u5) * lsdll(E5,F5,y5,u5,E3,F3,y3,u3) * lsdll(E4,F4,x5,u4,E6,F6,x6,u6) & u4 != u3
         |- lsdll(E1,F1,x1,u1,E3,F3,x3,u3) * lsdll(E2,F2,x2,u2,E6,F6,x6,u6).

