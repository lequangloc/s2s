
ddata RefAtll_t {
  RefAtll_t lson;
  RefAtll_t rson;
  RefAtll_t next;
}.

pred atll<r:RefAtll_t,ll:RefAtll_t,rl:RefAtll_t> ==
 r::RefAtll_t<lson = null,rson = null,next = rl> & r != rl & r = ll
or (exists ls,rs,z: r::RefAtll_t<lson = ls,rson = rs,next = null> * atll(ls,ll,z) * atll(rs,z,rl) & r != ll & r != rl).

pred R<x:RefAtll_t,y:RefAtll_t> ==
atll(x,null,y) * y::RefAtll_t<lson = null,rson = null,next = null>.

  checksat[unsat] R(x0,y0).

  //checksat[unsat] atll(x,null,y).

