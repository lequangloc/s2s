ddata node {
  node next;
}.


pred ls<x> == emp & x = null
  or exists u: x::node<u> * ls(u).

pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.



/*
//5a.
checkent[valid] lseg(x,y) * ls(t) & x!=y & z=x |- exists p: z::node<p> * lseg(p,y) *ls(t) .
*/

//1
checkent[valid] ls(x) & x!=null |- exists p: x::node<p> * ls(p) .


/*
//2
checkent[valid] ls(y) & x!=null & y=x |- exists p: x::node<p> * ls(p) .

//3
checkent[valid] ls(y) |- exists p2: ls(p2) & p2 =y.

//4a
checkent[valid] lseg(x,y) & x!=y |- exists p: x::node<p> * lseg(p,y) .

//4b
checkent[valid] lseg(x,y) & x!=y & z=x |- exists p: z::node<p> * lseg(p,y) .

//5b.
checkent[valid] lseg(x,y) * t::node<null> & x!=y & z=x |- exists p: z::node<p> * lseg(p,y) *ls(t) .



*/
