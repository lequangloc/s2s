
data Dll_t {
  Dll_t next;
  Dll_t prev;
}.

pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).


/*
pred dll<fr:Dll_t,bk:Dll_t,pr:Dll_t,nx:Dll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr = nx & bk = pr)
or (exists u: fr::Dll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).
*/

checkent[invalid] x_emp::Dll_t<next = w_emp,prev = null> * dll(w_emp,u_emp,x_emp,y_emp) * y_emp::Dll_t<next = z_emp,prev = _> & x_emp != w_emp & w_emp != y_emp
         |- dll(x_emp,y_emp,null,z_emp).

/*
RU x::Dll_t<next = w,prev = null> * dll(w,u,x,y) * y::Dll_t<next = z,prev = _> & x != w & w != y
 |- x::Dll_t<next = u1,prev = null> * dll(u1,y,x,z) & x != z & y != null

FR  dll(w,u,x,y) * y::Dll_t<next = z,prev = _> & x != w & w != y
 |-  dll(w,y,x,z) & x != z & y != null

LU1  y::Dll_t<next = z,prev = _> & x != w & w != y & w=y...
 |-  dll(w,y,x,z) & x != z & y != null

LU2 w::Dll_t<next = u2,prev = x> * dll(u2,u,w,y) * y::Dll_t<next = z,prev = _> & x != w & w != y & w != y & u != x
   |-  dll(w,y,x,z) & x != z & y != null
*/