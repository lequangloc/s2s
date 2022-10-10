data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

//dll-vc01

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent[valid]  dll(x_emp,y_emp,null,z_emp) & x_emp != z_emp
     |-    x_emp::Dll_t<next = y_emp,prev = null>  * y_emp::Dll_t<next = z_emp,prev = x_emp> & y_emp != z_emp & x_emp != null & y_emp != null & x_emp != y_emp .
