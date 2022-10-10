
data SL2_t {
  SL2_t n1;
  SL2_t n2;
}.

pred skl1<hd:SL2_t,ex:SL2_t> ==
 hd = ex
or (exists tl: hd::SL2_t<n2 = null,n1 = tl> * skl1(tl,ex) & hd != ex).

pred skl2<hd:SL2_t,ex:SL2_t> ==
 hd = ex
or (exists tl,Z1: hd::SL2_t<n2 = tl,n1 = Z1> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).

checkent[valid] x1::SL2_t<n2 = x2,n1 = x1_1> * x1_1::SL2_t<n2 = null,n1 = x1_2> * skl1(x1_2,x2) * x2::SL2_t<n2 = null,n1 = null>
         |- skl2(x1,null).

