
data RefDLL_t {
  RefDLL_t prev;
  RefDLL_t next;
}.

pred DLL_plus<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: hd::RefDLL_t<prev = p,next = x> * DLL_plus(x,hd,tl,n)).

pred DLL_plus_rev<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: tl::RefDLL_t<prev = x,next = n> * DLL_plus_rev(hd,p,x,tl)).

checkent[valid] (exists x,b,n: x::RefDLL_t<prev = b,next = n> * DLL_plus_rev(a,null,b,x) * DLL_plus(n,x,c,null))
         |- DLL_plus(a,null,c,null).

