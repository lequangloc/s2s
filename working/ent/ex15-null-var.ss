ddata node {
  node next;
}.



pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.

pred lseg1<x,p> == emp & x = p
  or exists u: x::node<u> * lseg1(u,p) & x!=p.


  //  checkent[valid]  emp & x=null |- lseg(x,null).

  //checksat[sat] lseg(x,null).

   checkent[valid] lseg(x,y) * lseg1(y,null) |- lseg(x,null) .

  //checkent[invalid] lseg(x,y) * lseg(y,z) |- lseg(x,z) .
