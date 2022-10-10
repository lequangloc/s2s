
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::RefDll_t<next = u,prev = pr> * dll(u,bk,fr,nx) & fr != nx & bk != pr).

checkent x::RefDll_t<next = x1,prev = null> * x1::RefDll_t<next = x2,prev = x> * x2::RefDll_t<next = x3,prev = x1> * x3::RefDll_t<next = x4,prev = x2> * x4::RefDll_t<next = y,prev = x3> * y::RefDll_t<next = z,prev = x4> & x != z & z != x1 & z != x2 & z != x3 & z != x4 & y != z
         |- dll(x,y,null,z).

