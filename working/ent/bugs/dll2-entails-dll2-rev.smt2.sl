
data DLL2_t {
  DLL2_t prev;
  DLL2_t next;
  DLL2_t prev2;
  DLL2_t next2;
  DLL2_t down;
}.

pred DLL2_plus<hd:DLL2_t,p:DLL2_t,tl:DLL2_t,n:DLL2_t> ==
 (exists down_hd: hd::DLL2_t<next2 = n,prev2 = p,down = down_hd> * DLL1_plus(down_hd,hd) & hd = tl)
or (exists x,down_hd: hd::DLL2_t<next2 = x,prev2 = p,down = down_hd> * DLL1_plus(down_hd,hd) * DLL2_plus(x,hd,tl,n)).


pred DLL2_plus_rev<hd:DLL2_t,p:DLL2_t,tl:DLL2_t,n:DLL2_t> ==
 (exists down_hd: hd::DLL2_t<next2 = n,prev2 = p,down = down_hd> * DLL1_plus(down_hd,hd) & hd = tl)
or (exists x,down_hd: tl::DLL2_t<next2 = n,prev2 = x,down = down_hd> * DLL1_plus(down_hd,tl) * DLL2_plus_rev(hd,p,x,tl)).


pred DLL1_plus<hd:DLL2_t,p:DLL2_t> ==
 (exists p1,p2: hd::DLL2_t<next = null,prev = p,prev2 = p1,next2 = p2,down = _>)
or (exists x,p1,p2: hd::DLL2_t<next = x,prev = p,prev2 = p1,next2 = p2,down = _> * DLL1_plus(x,hd)).


checkent[valid] DLL2_plus(x,y,u,v)
         |- DLL2_plus_rev(x,y,u,v).

