ddata node {
  int valVAL_11;
  node nextREC_21;
}.

 pred ll<self:node,n:int> == 
  emp&self=null & n=0 or
(exists flted_14_23: self::node<Anon_12,q> * 
  ll(q,flted_14_23)&flted_14_23+1=n)
//  inv 
//  0<=n
.

checksat  ll(x, i)&x'=x & 0<i & 3<4 & v_bool_96_2081'
 & 3<4  & !(v_bool_96_2081')
.