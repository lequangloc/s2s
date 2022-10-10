
ddata RefSll_t {
    RefSll_t next;
}.

pred ls<in,out> == 
    (emp & in=out)
     or (exists u: in::RefSll_t<next=u> * ls(u,out) & in!=out).

pred ls1<in,out> == 
    (emp & in=out)
     or (exists u: in::RefSll_t<next=u> * ls1(u,out) & in!=out).


checkent ls(x8,x12) * x12::RefSll_t<next=x2> * ls1(x11,x9) * ls(x6,x10) * x2::RefSll_t<next=x6> * ls1(x5,x9) * x3::RefSll_t<next=x4> * ls(x4,x8) * x1::RefSll_t<next=x6> * x10::RefSll_t<next=x1> * x9::RefSll_t<next=x7> * ls1(x7,x4) & null=null
    |- ls(x11,x9) * ls(x1,x6) * ls(x3,x4) * ls(x5,x8) * ls(x8,x1).
