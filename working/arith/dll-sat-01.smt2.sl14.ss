
data RefDll_t {
    RefDll_t next;
    RefDll_t prev;
}.

pred ldll<E,P,len1,F,L,len2> == 
    (emp & E=F & P=L & len1=len2)
     or (exists u,len3: E::RefDll_t<next=u,prev=P> * ldll(u,E,len3,F,L,len2) & len1=len3+1).


checksat[sat] y2::RefDll_t<next=x1,prev=y0> * ldll(x1,x2,n1,y1,y2,n2).
