
data node {
  node nxt;
}.

/*
pred elseg<in:node,p:node> ==
 emp & in = p
//or exists a,b: elseg(in,a) * a::node<nxt = b> * elseg(b,p) & in =p
or (exists a,b: in::node<nxt = a> * a::node<nxt = b> * elseg(b,p) & in =p)
or (exists a,b: in::node<nxt = a> * a::node<nxt = b> * elseg(b,p)).
*/


pred elseg<in:node,p:node> ==
  in = p
or (exists a,b: in::node<nxt = a> * a::node<nxt = b> * elseg(b,p)).


pred right<in:node,p:node> ==
(exists u: elseg(in,u) * elseg(u,p)).


checkent[invalid] x::node<nxt = a> * elseg(a,p)
         |- elseg(x,p).

/*
RU x::node<nxt = a> * elseg(a,p)
         |- x->u1 * u1 -> u2 * elseg(u2, p)
FR: elseg(a,p) |- a -> u2 * elseg(u2, p)
LU: 
*/
