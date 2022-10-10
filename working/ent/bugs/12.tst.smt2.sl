
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred ListO<x:GTyp,y:GTyp> ==
 x::GTyp<f0 = y,f1 = _> & null != x
or (exists xp: x::GTyp<f0 = xp,f1 = _> * ListE(xp,y) & null != x).

pred ListE<x:GTyp,y:GTyp> ==
(exists xp: x::GTyp<f0 = xp,f1 = _> * ListO(xp,y) & null != x).

checkent[valid] ListE(x,y) * ListO(y,z)
         |- ListO(x,z).

