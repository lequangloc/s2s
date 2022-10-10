data node {
  node next;
}.

pred ls<p,i> == emp & self = p & i=0
  or exists u: self::node<u> * u::ls<p,i-1>.

//checkentail x::tmp<k> |- exists y: x::ls<y,k>.
//checksat exists y: x::ls<y,k>.

checksat emp.

