data node2 {
  node2 l;
  node2 r;
}.

pred binPath<self, p> == emp & self=p
  or exists q: self::node2<_,q> * binPath(q, p)
  or exists q: self::node2<q,_> * binPath(q, p).


pred binTree<self> == emp & true
  or  exists l,r: self::node2<l,r> * binTree(l) * binTree(r).


pred binTreeSeg<self, b> == emp & self=b
  or exists c,d: self::node2<c,d> * binTreeSeg(c,b) * binTree(d)
  or exists c,d: self::node2<c,d> * binTree(c) * binTreeSeg(d,b).

//CYCLIC_SL


//17.
checkent[valid] binPath(x,y) |- binTreeSeg(x,y).

/*
//18.
checkent[valid] binTreeSeg(x,z) * binTreeSeg(z,y)  |- binTreeSeg(x,y).
*/
