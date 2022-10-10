
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred ls<x:GTyp,y:GTyp> ==
 x = y
or (exists xp: x::GTyp<f0 = xp,f1 = _> * ls(xp,y) & null != x & x != y).

checkent[valid] ls(x,y) * ls(y,null)
         |- ls(x,null).

