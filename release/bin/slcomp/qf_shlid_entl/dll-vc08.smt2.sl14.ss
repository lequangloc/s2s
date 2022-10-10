
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::RefDll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent w_emp::RefDll_t<next = t_emp,prev = u_emp> * dll(x_emp,u_emp,null,w_emp) * dll(t_emp,y_emp,w_emp,z_emp) & x_emp != w_emp & w_emp != t_emp & z_emp != w_emp
         |- dll(x_emp,y_emp,null,z_emp).

