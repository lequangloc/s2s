
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

checkent x1::RefSL2_t<n1 = x2,n2 = x2> * x2::RefSL2_t<n1 = null,n2 = null>
         |- skl2(x1,null).

