
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

checkent x1::RefNLL_lvl2_t<next2 = x2,down = x1_1> * x1_1::RefNLL_lvl1_t<next1 = x1_2> * lso(x1_2,x1_3) * x1_3::RefNLL_lvl1_t<next1 = null> * x2::RefNLL_lvl2_t<next2 = null,down = x2_1> * x2_1::RefNLL_lvl1_t<next1 = x2_2> * x2_2::RefNLL_lvl1_t<next1 = null>
         |- nll(x1,null,null).

