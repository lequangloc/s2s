
ddata RefTree_t {
  RefTree_t left;
  RefTree_t right;
}.

pred btree<x:RefTree_t,len1:int> ==
 emp & x = null & len1 = 0
or (exists l,r,n1,n2: x::RefTree_t<left = l,right = r> * btree(l,n1) * btree(r,n2) & len1 = n1+n2+1).

checksat btree(x,n1) & n1 = 320001.

