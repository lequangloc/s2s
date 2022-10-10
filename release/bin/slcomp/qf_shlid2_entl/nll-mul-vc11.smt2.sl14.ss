
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


checkent nll1(x1,x2,null) * x2::RefNLL_lvl2_t<next2=x3,down=x2_1> * lso(x2_1,null) * nll1(x3,null,null) * nll(x4,x5,null) * x5::RefNLL_lvl2_t<next2=x6,down=x1_2> * lso1(x1_2,null)
    |- nll(x4,x6,null) * nll1(x1,null,null).
