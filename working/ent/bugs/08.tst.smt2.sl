
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred BSLL<x:GTyp,y:GTyp> ==
 emp & x = y
or (exists xp,yp: xp::GTyp<f0 = yp,f1 = y> * BSLL(x,xp) & xp != null).

pred DLL<x:GTyp,y:GTyp,z:GTyp,w:GTyp> ==
 emp & x = y & z = w
or (exists zp: x::GTyp<f0 = zp,f1 = w> * DLL(zp,y,z,x) & null != x).


checkent[valid] DLL(a,b,c,d)
         |- BSLL(c,d).

/*
a::GTyp<u1,d> * DLL(u1,b,c,a) & null != a |-  BSLL(c,u2) * u2::GTyp<_,d> & u2!=null.
a::GTyp<u1,d> * u1::GTyp<u2,a> *  DLL(u2,b,c,u1) & null != a
*/