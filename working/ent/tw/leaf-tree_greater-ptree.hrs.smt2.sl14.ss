
ddata Refnode3 {
  Refnode3 f1;
  Refnode3 f2;
  Refnode3 f3;
}.

pred parent<x1:Refnode3,x2:Refnode3> ==
x1::Refnode3<f1 = null,f2 = null,f3 = x2>.

pred lroot<x1:Refnode3,x2:Refnode3,x3:Refnode3> ==
(exists r: x1::Refnode3<f1 = x2,f2 = r,f3 = x3> * tree(r,x1)).

pred rtree<x1:Refnode3,x2:Refnode3,x3:Refnode3> ==
 (exists r: x1::Refnode3<f1 = x3,f2 = r,f3 = x2> * parent(x3,x1) * tree(r,x1))
or (exists l,r: x1::Refnode3<f1 = l,f2 = r,f3 = x2> * rtree(l,x1,x3) * tree(r,x1)).

pred lltree<x1:Refnode3,x2:Refnode3,x3:Refnode3,x4:Refnode3> ==
 (exists p,r: x1::Refnode3<f1 = x2,f2 = r,f3 = p> * tree(r,x1) * lltree(p,x1,x3,x4))
or (exists r: x1::Refnode3<f1 = x2,f2 = r,f3 = x3> * tree(r,x1) * lroot(x3,x1,x4)).

pred tree<x1:Refnode3,x2:Refnode3> ==
 x1::Refnode3<f1 = null,f2 = null,f3 = x2>
or (exists y,z: x1::Refnode3<f1 = y,f2 = z,f3 = x2> * tree(y,x1) * tree(z,x1)).

pred grtree<x1:Refnode3,x2:Refnode3,x3:Refnode3> ==
(exists l,r: x1::Refnode3<f1 = l,f2 = r,f3 = x2> * rtree(l,x1,x3) * tree(r,x1)).

pred ltree<x1:Refnode3,x2:Refnode3,x3:Refnode3> ==
(exists p: x1::Refnode3<f1 = null,f2 = null,f3 = p> * lltree(p,x1,x2,x3)).


checkent[valid] ltree(x1,x2,x3)
         |- grtree(x2,x3,x1).


  /*
checksat lltree(p,x1,x2,x3).
  */
