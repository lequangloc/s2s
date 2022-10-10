data node {
  node next;
}.

pred olseg<self,p> ==  exists q: self::node<q> * elseg(q,p).

pred elseg<self, p> == emp & self=p
  or exists q: self::node<q> * olseg(q, p).

//CYCLIC_SL

//15
checkent[valid] olseg(x, z) * elseg(z, null) |- olseg(x, null).


/*
//14
checkent[valid] elseg(x,z) * elseg(z, null) |- elseg(x, null).



*/
/*
//13
checkent[valid] olseg(x,z) * olseg(z,null) |- elseg(x,null).
*/
/*
LU:1 x::node<q> * elseg(q,z) * olseg(z,null) |- elseg(x,null).
RU: 3 x::node<q> * elseg(q,z) * olseg(z,null) |- x::node<q> * olseg(q, null).
M: 4 elseg(q,z) * olseg(z,null) |- olseg(q, null)
LU1:5 olseg(z,null) & q=z |- olseg(q, null)
  M-PRED 7
LU2:6 q::node<q1> * olseg(q1, z) * olseg(z,null) |- olseg(q, null)
  RU: 8 q::node<q1> * olseg(q1, z) * olseg(z,null) |- q::node<q2> * elseg(q2,null)
  M-PTO: 9 olseg(q1, z) * olseg(z,null) |-  elseg(q1,null)
  CC
*/
