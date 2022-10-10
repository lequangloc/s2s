
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::RefDll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent x_emp::RefDll_t<next = w_emp,prev = z_emp> * w_emp::RefDll_t<next = y_emp,prev = x_emp> * y_emp::RefDll_t<next = u_emp,prev = w_emp> * u_emp::RefDll_t<next = z_emp,prev = y_emp> & x_emp != z_emp & w_emp != z_emp & y_emp != z_emp & u_emp != z_emp
         |- dll(x_emp,u_emp,z_emp,z_emp).

