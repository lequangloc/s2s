data node2 {
  node2 l;
  node2 r;
}.


pred binPath<self, p> == emp & self=p
  or exists q: self::node2<_,q> * binPath(q, p)
  or exists q: self::node2<q,_> * binPath(q, p).

//CYCLIC_SL

//16
checkent[valid] binPath(x, z) * binPath(z,y) |- binPath(x, y).

/*
LU1 binPath(z,y) & x=z |- binPath(x, y).
LU2  x::node2<_,q> * binPath(q, z) * binPath(z,y) |- binPath(x, y).
   RU
LU3  x::node2<q,_> * binPath(q, z) * binPath(z,y) |- binPath(x, y).
*/