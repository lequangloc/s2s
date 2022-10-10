
data RefSll_t {
    RefSll_t next;
    int data_;
}.

pred lsls<in,dt1,len1,out,dt2,len2> == 
    (emp & in=out & dt1=dt2 & len1=len2)
     or (exists u,dt3,len3: in::RefSll_t<next=u,data_=dt1> * lsls(u,dt3,len3,out,dt2,len2) & dt1<dt3+0 & len1=len3+1).


checksat[unsat] lsls(u_emp,d1,n1,z_emp,d2,n2) & d1=d2 & n1=n2+3.
