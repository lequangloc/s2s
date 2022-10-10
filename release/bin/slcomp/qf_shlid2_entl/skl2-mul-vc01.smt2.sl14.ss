
ddata RefSL2_t {
  RefSL2_t n1;
  RefSL2_t n2;
}.

pred skl1<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl: hd::RefSL2_t<n1 = tl,n2 = null> * skl1(tl,ex) & hd != ex).

pred skl2<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl,Z1: hd::RefSL2_t<n1 = Z1,n2 = tl> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).

pred skl11<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl: hd::RefSL2_t<n1 = tl,n2 = null> * skl11(tl,ex) & hd != ex).

pred skl21<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl,Z1: hd::RefSL2_t<n1 = Z1,n2 = tl> * skl11(Z1,tl) * skl21(tl,ex) & hd != ex).

checkent skl2(x4,x5) * skl21(x5,x6) * x1::RefSL2_t<n1 = x1_1,n2 = x2> * x1_1::RefSL2_t<n1 = x1_2,n2 = null> * skl1(x1_2,x2) * x2::RefSL2_t<n1 = null,n2 = null>
         |- skl21(x1,null) * skl2(x4,x6).

