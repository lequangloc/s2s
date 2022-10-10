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

pred skl12<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl: hd::RefSL2_t<n1 = tl,n2 = null> * skl12(tl,ex) & hd != ex).

pred skl22<hd:RefSL2_t,ex:RefSL2_t> ==
 emp & hd = ex
or (exists tl,Z1: hd::RefSL2_t<n1 = Z1,n2 = tl> * skl12(Z1,tl) * skl22(tl,ex) & hd != ex).

checkent[valid] skl2(x,null)
         |-skl1(x,null).

  /*
x::RefSL2_t<Z1,X1> * skl1(Z1,X1) * skl2(X1,null) & x != null
|=
x::RefSL2_t<Z1,X1> * skl1(Z1,null) & x != null & X1=null
   */
