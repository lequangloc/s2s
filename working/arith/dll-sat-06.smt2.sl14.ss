
data RefDll_t {
    RefDll_t next;
    RefDll_t prev;
    int data_;
}.

pred lsdll<E,P,dt1,len1,F,L,dt2,len2> == 
    (emp & E=F & P=L & dt1=dt2 & len1=len2)
     or (exists u,dt3,len3: E::RefDll_t<next=u,prev=P,data_=dt1> * lsdll(u,E,dt3,len3,F,L,dt2,len2) & dt1>dt3+1 & len1=len3+1).


checksat[sat] lsdll(x1,x2,d1,n1,y1,y2,d2,n2) * y1::RefDll_t<next=x3,prev=y2,data_=d2> * lsdll(x3,x4,d3,n3,y3,y4,d4,n4) & n2=n3+1 & n2>n4+1 & d1!=d2 & x4=y1.
