data node {
     node next;
}.

pred lseg<p,n> == self=p & n=0
  or self::node<q> * q::lseg<p,n-1>
  .

pred cll<n> == self=null & n=0
  or self::node<q> * q::lseg<self,n-1>
  .