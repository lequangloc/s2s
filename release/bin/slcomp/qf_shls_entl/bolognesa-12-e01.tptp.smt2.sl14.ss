
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x10::RefSll_t<next = x6> * x2::RefSll_t<next = x1> * x8::RefSll_t<next = x5> * x4::RefSll_t<next = x7> * x1::RefSll_t<next = x6> * x9::RefSll_t<next = x3> * x6::RefSll_t<next = x4> * ls(x12,x8) * x5::RefSll_t<next = x1> * x7::RefSll_t<next = x6> * x3::RefSll_t<next = x5> * ls(x11,x8) & null = null
         |- ls(x10,x6) * ls(x12,x8) * ls(x11,x5) * ls(x9,x5) * ls(x5,x1) * ls(x2,x4) * ls(x4,x6).

