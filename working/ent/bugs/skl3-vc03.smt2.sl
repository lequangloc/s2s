
data SL3_t {
  SL3_t n1;
  SL3_t n2;
  SL3_t n3;
}.

pred skl1<hd:SL3_t,ex:SL3_t> ==
 hd = ex
or (exists tl: hd::SL3_t<n2 = null,n1 = tl,n3 = _> * skl1(tl,ex) & hd != ex).

pred skl2<hd:SL3_t,ex:SL3_t> ==
 hd = ex
or (exists tl,Z1: hd::SL3_t<n2 = tl,n1 = Z1,n3 = _> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).

pred skl3<hd:SL3_t,ex:SL3_t> ==
 hd = ex
or (exists tl,Z1,Z2: hd::SL3_t<n3 = tl,n2 = Z2,n1 = Z1> * skl1(Z1,Z2) * skl2(Z2,tl) * skl3(tl,ex) & hd != ex).

checkent[valid] skl3(x1,x2) * x2::SL3_t<n3 = x3,n2 = x2_1,n1 = x2_0_1> * skl3(x3,null) * skl2(x2_1,x3) * skl1(x2_0_1,x2_1)
         |- skl3(x1,null).

