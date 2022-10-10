
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::RefDll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent x_emp::RefDll_t<next = y_emp,prev = null> * y_emp::RefDll_t<next = z_emp,prev = x_emp> & x_emp != z_emp & y_emp != z_emp & x_emp != null & y_emp != null & x_emp != y_emp
         |- dll(x_emp,y_emp,null,z_emp).

