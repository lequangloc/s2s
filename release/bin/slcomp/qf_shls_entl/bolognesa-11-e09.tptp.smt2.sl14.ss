
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x7> * x7::RefSll_t<next = x8> * x8::RefSll_t<next = x4> * x10::RefSll_t<next = x5> * x4::RefSll_t<next = x8> * x9::RefSll_t<next = x8> * x1::RefSll_t<next = x5> * x3::RefSll_t<next = x6> * x11::RefSll_t<next = x7> * x6::RefSll_t<next = x11> * ls(x2,x6) & null = null
         |- ls(x10,x5) * ls(x4,x8) * ls(x3,x6) * ls(x9,x8) * ls(x2,x7) * ls(x1,x4).

