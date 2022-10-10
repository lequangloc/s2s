
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x7,x2) * ls(x6,x5) * x4::RefSll_t<next = x1> * x5::RefSll_t<next = x8> * x3::RefSll_t<next = x9> * x11::RefSll_t<next = x3> * ls(x1,x4) * x13::RefSll_t<next = x3> * x12::RefSll_t<next = x10> * x10::RefSll_t<next = x7> * x9::RefSll_t<next = x4> * x8::RefSll_t<next = x7> * x2::RefSll_t<next = x12> & null = null
         |- ls(x6,x5) * ls(x10,x7) * ls(x13,x3) * ls(x1,x4) * ls(x11,x1) * ls(x5,x10).

