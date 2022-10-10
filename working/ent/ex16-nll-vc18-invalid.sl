
ddata RefNLL_lvl1_t {
  RefNLL_lvl1_t next1;
}.

ddata RefNLL_lvl2_t {
  RefNLL_lvl2_t next2;
  RefNLL_lvl1_t down;
}.

pred lso<in:RefNLL_lvl1_t,out:RefNLL_lvl1_t> ==
 emp & in = out
or (exists u: in::RefNLL_lvl1_t<next1 = u> * lso(u,out) & in != out).

pred nll<in:RefNLL_lvl2_t,out:RefNLL_lvl2_t,boundary:RefNLL_lvl1_t> ==
 emp & in = out
or (exists u,Z1: in::RefNLL_lvl2_t<next2 = u,down = Z1> * lso(Z1,boundary) * nll(u,out,boundary) & in != out).

pred lso1<in:RefNLL_lvl1_t,out:RefNLL_lvl1_t> ==
 emp & in = out
or (exists u: in::RefNLL_lvl1_t<next1 = u> * lso1(u,out) & in != out).

pred nll1<in:RefNLL_lvl2_t,out:RefNLL_lvl2_t,boundary:RefNLL_lvl1_t> ==
 emp & in = out
or (exists u,Z1: in::RefNLL_lvl2_t<next2 = u,down = Z1> * lso1(Z1,boundary) * nll1(u,out,boundary) & in != out).

checkent[invalid] nll(x1,x2,null) * x2::RefNLL_lvl2_t<next2 = x3,down = x2_1> * lso(x2_1,null) * nll(x3,null,null) * nll1(x4,x5,null) * x5::RefNLL_lvl2_t<next2 = x6,down = null>
         |- nll1(x4,x6,null) * nll(x1,null,null).

