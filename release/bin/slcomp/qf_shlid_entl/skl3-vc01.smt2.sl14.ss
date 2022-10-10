
ddata RefSL3_t {
  RefSL3_t n1;
  RefSL3_t n2;
  RefSL3_t n3;
}.

pred skl1<hd:RefSL3_t,ex:RefSL3_t> ==
 emp & hd = ex
or (exists tl: hd::RefSL3_t<n1 = tl,n2 = null,n3 = null> * skl1(tl,ex) & hd != ex).

pred skl2<hd:RefSL3_t,ex:RefSL3_t> ==
 emp & hd = ex
or (exists tl,Z1: hd::RefSL3_t<n1 = Z1,n2 = tl,n3 = null> * skl1(Z1,tl) * skl2(tl,ex) & hd != ex).

pred skl3<hd:RefSL3_t,ex:RefSL3_t> ==
 emp & hd = ex
or (exists tl,Z1,Z2: hd::RefSL3_t<n1 = Z1,n2 = Z2,n3 = tl> * skl1(Z1,Z2) * skl2(Z2,tl) * skl3(tl,ex) & hd != ex).

checkent x1::RefSL3_t<n1 = x2,n2 = x2,n3 = x2> * x2::RefSL3_t<n1 = null,n2 = null,n3 = null>
         |- skl3(x1,null).

