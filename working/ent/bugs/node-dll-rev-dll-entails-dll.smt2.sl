
data DLL_t {
  DLL_t prev;
  DLL_t next;
}.

pred DLL_plus<hd:DLL_t,p:DLL_t,tl:DLL_t,n:DLL_t> ==
 hd::DLL_t<next = n,prev = p> & hd = tl
or (exists x: hd::DLL_t<next = x,prev = p> * DLL_plus(x,hd,tl,n)).

pred DLL_plus_rev<hd:DLL_t,p:DLL_t,tl:DLL_t,n:DLL_t> ==
 hd::DLL_t<next = n,prev = p> & hd = tl
or (exists x: tl::DLL_t<next = n,prev = x> * DLL_plus_rev(hd,p,x,tl)).

/*
checkent[valid] (exists x,n,b: x::DLL_t<next = n,prev = b> * DLL_plus_rev(a,null,b,x) * DLL_plus(n,x,c,null))
         |- DLL_plus(a,null,c,null).
*/

checkent[valid] (exists x,n,b: x::DLL_t<next = n,prev = b> * DLL_plus(a,null,b,x) * DLL_plus(n,x,c,null))
         |- DLL_plus(a,null,c,null).
