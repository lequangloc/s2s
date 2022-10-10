
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


checkent x_emp::RefDll_t<next=w_emp,prev=null> * dll1(w_emp,y_emp,x_emp,z_emp) * y_emp::RefDll_t<next=z_emp,prev=null>
    |- dll(x_emp,y_emp,null,z_emp).
