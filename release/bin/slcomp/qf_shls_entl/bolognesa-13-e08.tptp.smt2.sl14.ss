
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x4,x6) * x9::RefSll_t<next = x12> * x5::RefSll_t<next = x7> * ls(x7,x9) * x13::RefSll_t<next = x8> * x8::RefSll_t<next = x1> * ls(x6,x5) * ls(x11,x13) * x3::RefSll_t<next = x8> * x10::RefSll_t<next = x3> * x12::RefSll_t<next = x1> * x2::RefSll_t<next = x7> * x1::RefSll_t<next = x11> & null = null
         |- ls(x10,x8) * ls(x8,x1) * ls(x4,x6) * ls(x6,x7) * ls(x2,x8).

