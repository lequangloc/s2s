
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x8::RefSll_t<next = x7> * ls(x7,x2) * x11::RefSll_t<next = x9> * x4::RefSll_t<next = x1> * x1::RefSll_t<next = x8> * ls(x6,x9) * x3::RefSll_t<next = x11> * x5::RefSll_t<next = x7> * ls(x9,x1) * x10::RefSll_t<next = x7> * ls(x2,x7) & null = null
         |- ls(x10,x7) * ls(x6,x9) * ls(x2,x7) * ls(x4,x1) * ls(x3,x7) * ls(x5,x2).

