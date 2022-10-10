
data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent[valid] x_emp::Dll_t<next = w_emp,prev = null> * dll(w_emp,u_emp,x_emp,y_emp) * y_emp::Dll_t<next = z_emp,prev = u_emp> & x_emp != w_emp & x_emp != z_emp & y_emp != z_emp
         |- dll(x_emp,y_emp,null,z_emp).


/*
LHS:
x::Dll_t<w,null> * dll(w,u,x,y) * y::Dll_t<z,u> & x != w & x != z & y != z

UNFOLD REC:
(exists u4: x::Dll_t<w,null> * w::Dll_t<u4,x> * dll(u4,u,w,y) * y::Dll_t<z,u> & x != w & x != z & y != z & w != y & u != x)

UNFOLD BASE:
(exists u4: x::Dll_t<w,null> * w::Dll_t<u4,x> * y::Dll_t<z,u> & x != w & x != z & y != z & w != y & u != x & u4=y & u=w)


==> can not imply w != z
*/

/*
dll(x_emp,y_emp,null,z_emp)

x::Dll_t<u1,null> * dll(u1,y,x,z) & x != z & y != null

x::Dll_t<w,null> * dll(w,y,x,z) & x != z & y != null

x::Dll_t<u1,null> *
u1::Dll_t<u2,x> * dll(u2,y,w,z) & w != z & y != x
 & x != z & y != null

*/