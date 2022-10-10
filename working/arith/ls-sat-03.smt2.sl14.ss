
data RefSll_t {
    RefSll_t next;
    int data_;
}.

pred sls<in,dt1,out,dt2> == 
    (emp & in=out & dt1=dt2)
     or (exists u,dt3: in::RefSll_t<next=u,data_=dt1> * sls(u,dt3,out,dt2) & dt1 < dt3+0).


checksat[sat] sls(x_emp,d0,z_emp,d1) * z_emp::RefSll_t<next=y_emp,data_=d1> * sls(y_emp,d1,w_emp,d2) & d0!=d1 & d1!=d2.
