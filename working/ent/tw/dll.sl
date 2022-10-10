ddata RefDLL_t {
  RefDLL_t prev;
  RefDLL_t next;
}.

/*
pred DLL<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 emp & p = tl & hd = n
or (exists x: hd::RefDLL_t<prev = p,next = x> * DLL(x,hd,tl,n)).
*/

pred DLL_plus<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: hd::RefDLL_t<prev = p,next = x> * DLL_plus(x,hd,tl,n)).

pred DLL_plus_rev<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: tl::RefDLL_t<prev = x,next = n> * DLL_plus_rev(hd,p,x,tl)).


checkent[valid] DLL_plus(hd0,null,tl0,hd1)
         |- DLL_plus_rev(hd0,null,tl0,hd1).

/*
checkent[invalid] DLL(hd0,null,tl0,hd1)
         |- DLL_plus_rev(hd0,null,tl0,hd1).
*/

/*
checkent[valid] DLL_plus_rev(hd0,null,tl0,hd1)
         |- DLL(hd0,null,tl0,hd1).
*/