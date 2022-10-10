
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x6,x13) * x8::RefSll_t<next = x1> * x7::RefSll_t<next = x16> * x17::RefSll_t<next = x1> * ls(x11,x19) * x16::RefSll_t<next = x11> * x2::RefSll_t<next = x5> * x15::RefSll_t<next = x7> * ls(x5,x19) * ls(x19,x12) * x9::RefSll_t<next = x14> * x18::RefSll_t<next = x11> * ls(x4,x16) * x13::RefSll_t<next = x2> * x14::RefSll_t<next = x10> * x3::RefSll_t<next = x17> * x10::RefSll_t<next = x5> * x12::RefSll_t<next = x14> * x1::RefSll_t<next = x5> & null = null
         |- ls(x8,x1) * ls(x9,x14) * ls(x6,x2) * ls(x2,x5) * ls(x3,x17) * ls(x17,x5) * ls(x15,x16) * ls(x4,x16) * ls(x16,x11) * ls(x18,x19) * ls(x19,x12) * ls(x12,x19).

