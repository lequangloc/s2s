
data RefDll_t {
    RefDll_t next;
    RefDll_t prev;
    int data_;
}.

pred sdll<E,P,dt1,F,L,dt2> == 
    (emp & E=F & P=L & dt1=dt2)
     or (exists u,dt3: E::RefDll_t<next=u,prev=P,data_=dt1> * sdll(u,E,dt3,F,L,dt2) & dt1>dt3+1).

checksat[sat] sdll(x1,x2,d1,y1,y2,d2) & d1 > d2+3 & x1=y2.
