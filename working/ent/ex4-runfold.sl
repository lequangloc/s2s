ddata node {
  node next;
}.


pred ls<x> == emp & x = null
  or exists u: x::node<u> * ls(u).


pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.

pred lseg1<x,p> == emp & x = p
  or exists u: x::node<u> * lseg1(u,p) & x!=p.


//checkent[invalid] lseg(x,y) * lseg(y,z) |- lseg(x,z) .

//checkent[valid] lseg(x,y) * lseg(y,null) |- lseg(x,null) .

//tofix
//checkent[valid] lseg(x,y) * lseg1(y,null) |- lseg(x,null) .

//checkent[valid]  lseg1(x,null) |- lseg(x,null) .

checkent[valid]  emp & x=null |- lseg(x,null) .

/*
//1a
checkent[valid] emp & x=null |- ls(x) .

//1b
checkent[valid] x::node<null> |- ls(x) .

//1c
checkent[invalid] x::node<u> |- ls(x) .

//1d
checkent[invalid] (exists u1: x::node<u1> & u1=u2 & u2=null) |- ls(x) .

//2a.
checkent[valid] ls(y) & x=null |- ls(x) & y=null.

//2c1.
checkent[invalid] ls(y)  & z=null |- ls(z)  & y=null.

//2c.
checkent[invalid] ls(y) * ls(x) * t::node<x> & x=null & x=x2 & z=null |- ls(z) * t::node<null> & y=null & x2=null.

//2b.
checkent[invalid] ls(y) * ls(x) & x=null & x=x2 & z=null |- ls(z) & y=null & x2=null.



//2d.
checkent[valid]  t::node<x> * t2::node<t> & x=null  |-  exists x2,t3: t2::node<t3> * t3::node<x2> & x2=null.

*/
