
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x10::RefSll_t<next = x7> * x2::RefSll_t<next = x4> * ls(x6,x1) * ls(x1,x11) * ls(x12,x10) * x5::RefSll_t<next = x7> * ls(x3,x10) * ls(x9,x10) * x4::RefSll_t<next = x12> * ls(x7,x5) * ls(x11,x10) * x8::RefSll_t<next = x9> & null = null
         |- ls(x5,x7) * ls(x2,x4) * ls(x8,x9) * ls(x9,x10) * ls(x6,x1) * ls(x4,x10) * ls(x3,x10) * ls(x1,x5).

