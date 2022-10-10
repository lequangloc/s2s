
data RefTll_t {
  RefTll_t lson;
  RefTll_t rson;
  RefTll_t next;
}.

pred tll<r:RefTll_t,ll:RefTll_t,rl:RefTll_t> ==
 r::RefTll_t<lson = null,rson = null,next = rl> & r = ll
or (exists ls,rs,z: r::RefTll_t<lson = ls,rson = rs,next = null> * tll(ls,ll,z) * tll(rs,z,rl)).

/*
checkent[valid] tll(x0,null,null)
         |- false.
*/

checksat[unsat] tll(x0,null,null).