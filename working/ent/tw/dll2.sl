ddata RefDLL2_t {
  RefDLL2_t prev;
  RefDLL2_t next;
  RefDLL2_t prev2;
  RefDLL2_t next2;
  RefDLL2_t down;
}.

pred DLL1_plus<hd:RefDLL2_t,p:RefDLL2_t> ==
 hd::RefDLL2_t<prev = p,next = null,prev2 = null,next2 = null,down = null>
or (exists x: hd::RefDLL2_t<prev = p,next = x,prev2 = null,next2 = null,down = null> * DLL1_plus(x,hd)).

pred DLL2_plus<hd:RefDLL2_t,p:RefDLL2_t,tl:RefDLL2_t,n:RefDLL2_t> ==
 (exists down_hd: hd::RefDLL2_t<prev = null,next = null,prev2 = p,next2 = n,down = down_hd> * DLL1_plus(down_hd,hd) & hd = tl)
or (exists x,down_hd: hd::RefDLL2_t<prev = null,next = null,prev2 = p,next2 = x,down = down_hd> * DLL1_plus(down_hd,hd) * DLL2_plus(x,hd,tl,n)).

pred DLL2_plus_rev<hd:RefDLL2_t,p:RefDLL2_t,tl:RefDLL2_t,n:RefDLL2_t> ==
 (exists down_hd: hd::RefDLL2_t<prev = null,next = null,prev2 = p,next2 = n,down = down_hd> * DLL1_plus(down_hd,hd) & hd = tl)
or (exists x,down_hd: tl::RefDLL2_t<prev = null,next = null,prev2 = x,next2 = n,down = down_hd> * DLL1_plus(down_hd,tl) * DLL2_plus_rev(hd,p,x,tl)).

checkent[valid] DLL2_plus(a,b,c,d) |- DLL2_plus_rev(a,b,c,d).