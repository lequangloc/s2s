data node {
  node next;
}.

data node2 {
  node2 left;
  node2 right;
}.

pred bt<x> == emp & x = null
  or exists l,r: x::node2<l,r> * bt(l) * bt(r).


pred lseg<x,p> == emp & x = p
  or exists u: x::node<u> * lseg(u,p) & x!=p.

pred rlseg<x,y> == emp & x = y
  or exists u: rlseg(x,u) *  u::node<y>.

pred nlseg<x,p> == x::node<p>
  or exists u: x::node<u> * nlseg(u,p).

pred glseg<x,p> == emp & x = p
  or exists u: x::node<u> * glseg(u,p).



//1 E1
checkent[valid] lseg(x,y) * lseg(y, null) |- lseg(x, null) .

//2 E2
checkent[valid] lseg(x,t) * t::node<y> * lseg(y, null) |- lseg(x, null) .

//3 E3
checkent[valid] lseg(x,y) * lseg(y, t) * t::node<null> |- lseg(x, null) .

//4 E4
checkent[valid] lseg(x,y) * lseg(y, t) * bt(t) & t!=null |- lseg(x, t) * bt(t).

//5 E5
checkent[valid] lseg(x,y) * lseg(y, t) * lseg(t, z) & t!=z |- lseg(x, t) * lseg(t, z).

//6 E6
checkent[valid] x::node<y> * rlseg(y,z) |- rlseg(x,z).

//7 E7.
checkent[valid] nlseg(x,t) * t::node<y> |- nlseg(x, y).

//8 E8
checkent[valid] nlseg(x,t) * nlseg(t, y)  |- nlseg(x, y).

//9 E9
checkent[valid] glseg(x,t) * t::node<y>   |- glseg(x, y).

//10 E10
checkent[valid] glseg(x,t) * glseg(t, y)  |- glseg(x, y).
