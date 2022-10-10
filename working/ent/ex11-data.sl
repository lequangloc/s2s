data node {
  int val;
  node next;
}.


pred lseg<self,p> == emp & self=p
  or (exists q: self::node<_,q> * lseg(q,p) & self!=p).


//1.
checkent[valid] lseg(x,p1) * lseg(p1,null) |- lseg(x,null).



/*

//1a. OK
checkent[valid]  x::node<_,null> |- x::node<_,q>.

//1b. RUNFOLD
checkent[valid]  x::node<_,null> |- exists p: lseg(x,p).

//1c. CC
checkent[valid]  lseg(x,y) * y::node<_,null> |-  lseg(x,null).

//1d. match
checkent[valid] exists d,y: x::node<d,y> * lseg(y,null) & x!=null |-  lseg(x,null).

//1e. pred match with eqs and nulls
checkent[valid] exists r1: lseg(p1,r1) & x=p1 & r1=null |- exists r2: lseg(x,r2) & r2=null.
*/