data node {
     node next;
}.

pred oll<n> == self::node<null> & n=1
     or self::node<q> * q::node<p> * p::oll<n-2>
     .