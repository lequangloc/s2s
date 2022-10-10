
data RefDLL_t {
  RefDLL_t prev;
  RefDLL_t next;
}.

pred DLL<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 emp & p = tl & hd = n
or (exists x: hd::RefDLL_t<prev = p,next = x> * DLL(x,hd,tl,n)).

pred DLL_plus<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: hd::RefDLL_t<prev = p,next = x> * DLL_plus(x,hd,tl,n)).

pred DLL_plus_rev<hd:RefDLL_t,p:RefDLL_t,tl:RefDLL_t,n:RefDLL_t> ==
 hd::RefDLL_t<prev = p,next = n> & hd = tl
or (exists x: tl::RefDLL_t<prev = x,next = n> * DLL_plus_rev(hd,p,x,tl)).

checkent[valid] DLL_plus(hd0,null,tl0,hd1) * DLL_plus(hd1,tl0,tl1,hd2) * DLL_plus(hd2,tl1,tl2,hd3) * DLL_plus(hd3,tl2,tl3,hd4) * DLL_plus(hd4,tl3,tl4,hd5) * DLL_plus(hd5,tl4,tl5,hd6) * DLL_plus(hd6,tl5,tl6,hd7) * DLL_plus(hd7,tl6,tl7,hd8) * DLL_plus(hd8,tl7,tl8,hd9) * DLL_plus(hd9,tl8,tl9,hd10) * DLL_plus(hd10,tl9,tl10,hd11) * DLL_plus(hd11,tl10,tl11,hd12) * DLL_plus(hd12,tl11,tl12,hd13) * DLL_plus(hd13,tl12,tl13,hd14) * DLL_plus(hd14,tl13,tl14,hd15) * DLL_plus(hd15,tl14,tl15,hd16) * DLL_plus(hd16,tl15,tl16,hd17) * DLL_plus(hd17,tl16,tl17,hd18) * DLL_plus(hd18,tl17,tl18,hd19) * DLL_plus(hd19,tl18,tl19,hd20) * DLL_plus(hd20,tl19,tl20,null)
         |- (exists hd1,tl1,hd2,tl2,hd3,tl3,hd4,tl4,hd5,tl5,hd6,tl6,hd7,tl7,hd8,tl8,hd9,tl9,hd10,tl10,hd11,tl11,hd12,tl12,hd13,tl13,hd14,tl14,hd15,tl15,hd16,tl16,hd17,tl17,hd18,tl18,hd19,tl19: DLL_plus_rev(hd0,null,tl0,hd1) * DLL_plus_rev(hd1,tl0,tl1,hd2) * DLL_plus_rev(hd2,tl1,tl2,hd3) * DLL_plus_rev(hd3,tl2,tl3,hd4) * DLL_plus_rev(hd4,tl3,tl4,hd5) * DLL_plus_rev(hd5,tl4,tl5,hd6) * DLL_plus_rev(hd6,tl5,tl6,hd7) * DLL_plus_rev(hd7,tl6,tl7,hd8) * DLL_plus_rev(hd8,tl7,tl8,hd9) * DLL_plus_rev(hd9,tl8,tl9,hd10) * DLL_plus_rev(hd10,tl9,tl10,hd11) * DLL_plus(hd11,tl10,tl11,hd12) * DLL_plus(hd12,tl11,tl12,hd13) * DLL_plus(hd13,tl12,tl13,hd14) * DLL_plus(hd14,tl13,tl14,hd15) * DLL_plus(hd15,tl14,tl15,hd16) * DLL_plus(hd16,tl15,tl16,hd17) * DLL_plus(hd17,tl16,tl17,hd18) * DLL_plus(hd18,tl17,tl18,hd19) * DLL_plus(hd19,tl18,tl19,hd20) * DLL_plus(hd20,tl19,tl20,null)).

