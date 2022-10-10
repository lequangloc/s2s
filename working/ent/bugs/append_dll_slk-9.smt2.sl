
data node2 {
  node2 prev;
  node2 next;
}.

pred dll<in:node2,p:node2> ==
 in = null
or (exists p_20,self_21,q_19: in::node2<prev = p_20,next = q_19> * dll(q_19,self_21) & p_20 = p & self_21 = in).

pred dll_e1<in:node2,q:node2> ==
(exists p1,s,q1: dll(q1,s) * in::node2<prev = p1,next = q1> & in = s & p1 = q).

pred dll_e2<in:node2,q:node2> ==
(exists s,p1,p2,n,q1: in::node2<prev = p1,next = n> * dll(q1,s) & n = q1 & p1 = p2 & s = in & p2 = q).

pred node2_e1<in:node2,p:node2,q:node2> ==
(exists p1,n1: in::node2<prev = p1,next = n1> & p1 = p & n1 = q).

pred dll_e3<in:node2,p:node2> ==
(exists q: dll(in,q) & q = p).

checkent[valid] dll(q,self) * dll(y,p) * xprm::node2<prev = p1,next = q> & v1prm = q & q != null & xprm = x & yprm = y & x != null & self = xprm & p1 = q1
         |- dll_e3(v1prm,self) * dll_e3(yprm,p) * xprm::node2<prev = p1,next = q> & v1prm = q & q != null & xprm = x & yprm = y & x != null & self = xprm & p1 = q1 & v1prm != null.

