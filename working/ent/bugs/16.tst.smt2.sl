
data GTyp {
  GTyp f0;
  GTyp f1;
}.

pred BinPath<x:GTyp,y:GTyp> ==
 x = y
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinPath(xp,y) & null != x)
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinPath(yp,y) & null != x).

pred BinTree<x:GTyp> ==
 emp
or (exists yp,xp: x::GTyp<f0 = yp,f1 = xp> * BinTree(yp) * BinTree(xp) & null != x).

pred BinTreeSeg<x:GTyp,y:GTyp> ==
 x = y
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinTreeSeg(xp,y) * BinTree(yp) & null != x)
or (exists xp,yp: x::GTyp<f0 = xp,f1 = yp> * BinTree(xp) * BinTreeSeg(yp,y) & null != x).

checkent[valid] BinPath(x,y)
         |- BinTreeSeg(x,y).

