data SL2_t {
  SL2_t n1;
  SL2_t n2;
}.

pred skl1<hd:SL2_t,ex:SL2_t> ==
emp & hd = ex
or (exists tl: hd::SL2_t<n2 = null,n1 = tl> * skl1(tl,ex) & hd != ex).

pred skl2<hd:SL2_t,ex:SL2_t> ==
emp & hd = ex
or (exists tl,Z1: hd::SL2_t<n2 = tl,n1 = Z1> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).

//456+skl2vc04

checkent[invalid] skl2(x4,x5) * skl2(x5,x6) * x1::SL2_t<n2 = x2,n1 = x1_1> * x1_1::SL2_t<n2 = null,n1 = x1_2> * skl1(x1_2,x2) * x2::SL2_t<n2 = null,n1 = null>
         |-  skl2(x4,x6) * skl2(x1,null) .
