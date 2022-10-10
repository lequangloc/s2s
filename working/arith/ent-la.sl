
data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t, n> ==
 emp & fr = nx & bk = pr & n=0
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx,n-1) & fr != nx & bk != pr).

checkent[valid] x_emp::Dll_t<next = w_emp,prev = null> * w_emp::Dll_t<next = y_emp,prev = x_emp> * y_emp::Dll_t<next = z_emp,prev = w_emp> & x_emp != z_emp & w_emp != z_emp & y_emp != z_emp
         |- dll(x_emp,y_emp,null,z_emp,3).

