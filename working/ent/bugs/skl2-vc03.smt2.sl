
data SL2_t {
  SL2_t n1;
  SL2_t n2;
}.

pred skl1<hd:SL2_t,ex:SL2_t> ==
 hd = ex
//or (exists tl: hd::SL2_t<n2 = null,n1 = tl> * skl1(tl,ex) & hd = ex)
or (exists tl: hd::SL2_t<n2 = null,n1 = tl> * skl1(tl,ex) & hd != ex).

pred skl2<hd:SL2_t,ex:SL2_t> ==
 hd = ex
or (exists tl,Z1: hd::SL2_t<n2 = tl,n1 = Z1> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).


checkent[valid] x1::SL2_t<n2 = x2,n1 = x1_1> * x1_1::SL2_t<n2 = null,n1 = x1_2> * x1_2::SL2_t<n2 = null,n1 = x1_3> * x1_3::SL2_t<n2 = null,n1 = x1_4> * x1_4::SL2_t<n2 = null,n1 = x2> * skl2(x2,x3) * x3::SL2_t<n2 = null,n1 = x3_1> * x3_1::SL2_t<n2 = null,n1 = x3_2> * x3_2::SL2_t<n2 = null,n1 = null>
         |- skl2(x1,null).

