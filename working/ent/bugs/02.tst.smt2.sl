
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred RList<x:GTyp,y:GTyp> ==
 x::GTyp<f0 = y,f1 = _> & null != x
or (exists xp: xp::GTyp<f0 = y,f1 = _> * RList(x,xp) & xp != null).

checkent[valid] RList(x,y) * RList(y,z)
         |- RList(x,z).
/*
LU: RList(x,u1) * u1::GTyp<y> * RList(y,z) |- RList(x,z).
RU: RList(x,u1) * u1::GTyp<y> * RList(y,z) |- RList(x,u2) * u2::GTyp<z>.
*/
