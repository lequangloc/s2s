
data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent[valid] w_emp::Dll_t<next = t_emp,prev = u_emp> * dll(x_emp,u_emp,y_emp,w_emp) * dll(t_emp,y_emp,w_emp,x_emp) & w_emp != x_emp & w_emp != t_emp & y_emp != w_emp
         |- dll(x_emp,y_emp,y_emp,x_emp).

