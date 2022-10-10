
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred DLL<x:GTyp,y:GTyp,z:GTyp,w:GTyp> ==
 x = y & z = w
or (exists zp: x::GTyp<f0 = zp,f1 = w> * DLL(zp,y,z,x) & null != x).

checkent[valid] DLL(x,y,z,w) * DLL(a,x,w,b)
         |- DLL(a,y,z,b).

