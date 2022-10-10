
data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

//dll-vc01,vc04

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent[invalid] x_emp::Dll_t<next = w_emp,prev = null> * w_emp::Dll_t<next = y_emp,prev = x_emp> * y_emp::Dll_t<next = z_emp,prev = w_emp> * x2_emp::Dll_t<next = w2_emp,prev = null> * dll(w2_emp,y2_emp,null,z2_emp) & x_emp != z_emp & w_emp != z_emp & y_emp != z_emp &
x2_emp != w2_emp
         |- dll(x_emp,y_emp,null,z_emp) *  dll(x2_emp,y2_emp,null,z2_emp).

