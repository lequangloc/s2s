
ddata RefNLL_lvl1_t {
    RefNLL_lvl1_t next1;
}.

ddata RefNLL_lvl2_t {
    RefNLL_lvl2_t next2;
    RefNLL_lvl1_t down;
}.

pred lso<in,out> == 
    (emp & in=out)
     or (exists u: in::RefNLL_lvl1_t<next1=u> * lso(u,out) & in!=out).

pred nll<in,out,boundary> == 
    (emp & in=out)
     or (exists u,Z1: in::RefNLL_lvl2_t<next2=u,down=Z1> * lso(Z1,boundary) * nll(u,out,boundary) & in!=out).

pred lso1<in,out> == 
    (emp & in=out)
     or (exists u: in::RefNLL_lvl1_t<next1=u> * lso1(u,out) & in!=out).

pred nll1<in,out,boundary> == 
    (emp & in=out)
     or (exists u,Z1: in::RefNLL_lvl2_t<next2=u,down=Z1> * lso1(Z1,boundary) * nll1(u,out,boundary) & in!=out).


checkent nll(x1,x2,null) * x2::RefNLL_lvl2_t<next2=x3,down=x2_1> * x2_1::RefNLL_lvl1_t<next1=x2_2> * x2_2::RefNLL_lvl1_t<next1=x2_1> * nll1(x3,null,null)
    |- nll1(x1,null,null).
