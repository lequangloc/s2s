
data RefDll_t {
    RefDll_t next;
    RefDll_t prev;
    int data_;
}.

/*
pred lsdll0<E,P,dt1,len1,F,L,dt2,len2> == 
    (emp & E=F & P=L  & len1=len2)
     or (exists u,dt3,len3: E::RefDll_t<next=u,prev=P,data_=dt1> * lsdll0(u,E,dt3,len3,F,L,dt2,len2)  & len1=len3+1).
*/
/*
pred lsdll1<E,P,dt1,len1,F,L,dt2,len2> == 
    (emp & E=F & P=L & dt1=dt2 )
     or (exists u,dt3,len3: E::RefDll_t<next=u,prev=P,data_=dt1> * lsdll1(u,E,dt3,len3,F,L,dt2,len2) & dt1>dt3+1 ).
*/

pred lsdll<E,P,dt1,len1,F,L,dt2,len2> == 
    (emp & E=F & P=L & dt1=dt2 & len1=len2)
     or (exists u,dt3,len3: E::RefDll_t<next=u,prev=P,data_=dt1> * lsdll(u,E,dt3,len3,F,L,dt2,len2) & dt1>dt3+1 & len1=len3+1).

