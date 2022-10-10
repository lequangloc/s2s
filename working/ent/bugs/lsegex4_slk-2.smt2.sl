
data node {
  node nxt;
}.

pred lseg<in:node,p:node> ==
  in = p
or (exists a: in::node<nxt = a> * lseg(a,p)).

pred right1<in:node,p:node> ==
(exists u: lseg(in,u) * u::node<nxt = p>).

pred right2<in:node,p:node> ==
(exists u: lseg(in,u) * lseg(u,p)).

pred right3<in:node,p:node> ==
(exists u,u2: lseg(in,u) * lseg(u,u2) * lseg(u2,p)).

pred right4<in:node> ==
(exists u,w: lseg(in,u) * lseg(u,w)).

pred right5<in:node> ==
(exists w: lseg(in,w)).

checkent[invalid] lseg(x,p)
         |- right1(x,p).

