
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x25,x26) * ls(x26,x27) * x20::RefSll_t<next = x1> * x16::RefSll_t<next = x10> * x1::RefSll_t<next = x3> * x2::RefSll_t<next = x3> * x8::RefSll_t<next = x1> * ls(x13,x9) * x12::RefSll_t<next = x8> * x18::RefSll_t<next = x19> * x15::RefSll_t<next = x7> * x3::RefSll_t<next = x16> * x19::RefSll_t<next = x9> * x10::RefSll_t<next = x8> * x17::RefSll_t<next = x3> * x11::RefSll_t<next = x19> * x6::RefSll_t<next = x13> * ls(x7,x13) * x14::RefSll_t<next = x5> * x9::RefSll_t<next = x2> * x4::RefSll_t<next = x6> * x5::RefSll_t<next = x18> & null = null
         |- ls(x20,x1) * ls(x4,x13) * ls(x17,x3) * ls(x14,x18) * ls(x18,x19) * ls(x12,x8) * ls(x11,x9) * ls(x1,x3) * ls(x15,x1) * ls(x25,x27).

