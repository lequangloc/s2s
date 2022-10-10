
ddata RefDll_t {
    RefDll_t next;
    RefDll_t prev;
}.

pred dll<fr,bk,pr,nx> == 
    (emp & fr=nx & bk=pr)
     or (exists u: fr::RefDll_t<next=u,prev=pr> * dll(u,bk,fr,nx) & fr!=nx & bk!=pr).

pred dll1<fr,bk,pr,nx> == 
    (emp & fr=nx & bk=pr)
     or (exists u: fr::RefDll_t<next=u,prev=pr> * dll1(u,bk,fr,nx) & fr!=nx & bk!=pr).


checkent x_emp::RefDll_t<next=w_emp,prev=null> * dll1(w_emp,u_emp,x_emp,y_emp) * y_emp::RefDll_t<next=z_emp,prev=u_emp> * x2_emp::RefDll_t<next=w2_emp,prev=null> * dll(w2_emp,y2_emp,null,z2_emp) & x2_emp!=w2_emp & x_emp!=w_emp & x_emp!=z_emp & y_emp!=z_emp
    |- dll(x_emp,y_emp,null,z_emp) * dll1(x2_emp,y2_emp,null,z2_emp) & z_emp=z_emp.
