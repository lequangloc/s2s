
ddata RefSll_t {
    RefSll_t next;
}.

pred ls<in,out> == 
    (emp & in=out)
     or (exists u: in::RefSll_t<next=u> * ls(u,out) & in!=out).

pred ls1<in,out> == 
    (emp & in=out)
     or (exists u: in::RefSll_t<next=u> * ls1(u,out) & in!=out).


checkent x17::RefSll_t<next=x15> * ls(x6,x15) * x10::RefSll_t<next=x15> * ls(x5,x2) * x8::RefSll_t<next=x10> * x1::RefSll_t<next=x4> * x2::RefSll_t<next=x1> * x16::RefSll_t<next=x15> * x9::RefSll_t<next=x1> * ls1(x15,x3) * ls(x3,x5) * x7::RefSll_t<next=x14> * x11::RefSll_t<next=x2> * x12::RefSll_t<next=x3> * x14::RefSll_t<next=x2> * x13::RefSll_t<next=x14> * x4::RefSll_t<next=x7> & null=null
    |- ls(x13,x14) * ls(x11,x2) * ls(x17,x15) * ls(x16,x15) * ls(x8,x10) * ls(x9,x4) * ls1(x10,x15) * ls(x6,x3) * ls(x12,x2) * ls1(x4,x1).
