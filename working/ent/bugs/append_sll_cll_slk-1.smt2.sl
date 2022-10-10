
data node {
  node next;
}.

pred lseg<in:node,p:node> ==
 in = p
or (exists p_21,q_20: in::node<next = q_20> * lseg(q_20,p_21) & p_21 = p).

pred ll<in:node> ==
 in = null
or (exists q_22: in::node<next = q_22> * ll(q_22)).

pred clist<in:node> ==
(exists self_19,p_18: in::node<next = p_18> * lseg(p_18,self_19) & self_19 = in).

pred ll_e1<in:node> ==
(exists q: in::node<next = q> * ll(q)).

pred ll_e2<in:node> ==
(exists p,q: in::node<next = p> * ll(q) & p = q).

pred node_e1<in:node,q:node> ==
(exists p: in::node<next = p> & p = q).

pred lseg_e1<in:node,p:node> ==
(exists q: lseg(in,p) & p = q).

checkent[valid] ll_e1(xprm) & xprm = x & yprm = y & x != null
         |- ll_e2(xprm) & xprm = x & yprm = y & x != null.

