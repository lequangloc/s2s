
data NLL_lvl1_t {
  NLL_lvl1_t next1;
}.

data NLL_lvl2_t {
  NLL_lvl2_t next2;
  NLL_lvl1_t down;
}.


pred lso<in:NLL_lvl1_t,out:NLL_lvl1_t> ==
 in = out
//   emp & in = out
//or (exists u: in::NLL_lvl1_t<next1 = u> * lso(u,out) & in = out)
or (exists u: in::NLL_lvl1_t<next1 = u> * lso(u,out) & in != out).

pred nll<in:NLL_lvl2_t,out:NLL_lvl2_t,boundary:NLL_lvl1_t> ==
 in = out
or (exists u,Z1: in::NLL_lvl2_t<next2 = u,down = Z1> * lso(Z1,boundary) * nll(u,out,boundary) & in != out).


checkent[valid]
 x1::NLL_lvl2_t<next2 = x2,down = x1_1> *
     x1_1::NLL_lvl1_t<next1 = x1_2> * x1_2::NLL_lvl1_t<next1 = x1_3> * x1_3::NLL_lvl1_t<next1 = null> *
 x2::NLL_lvl2_t<next2 = null,down = x2_1> *
     x2_1::NLL_lvl1_t<next1 = x2_2> * x2_2::NLL_lvl1_t<next1 = null>

         |- nll(x1,null,null).

