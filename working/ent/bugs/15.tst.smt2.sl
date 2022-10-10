
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred BinPath<x:GTyp,y:GTyp> ==
 x = y
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinPath(xp,y) & null != x)
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinPath(yp,y) & null != x).


checkent[valid] BinPath(x,z) * BinPath(z,y)
         |- BinPath(x,y).

