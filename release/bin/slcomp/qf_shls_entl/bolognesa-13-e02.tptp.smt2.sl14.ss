
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x1::RefSll_t<next = x3> * x13::RefSll_t<next = x7> * x8::RefSll_t<next = x9> * x12::RefSll_t<next = x5> * ls(x7,x5) * x10::RefSll_t<next = x13> * ls(x9,x2) * x2::RefSll_t<next = x5> * x6::RefSll_t<next = x13> * x3::RefSll_t<next = x9> * x11::RefSll_t<next = x3> * x4::RefSll_t<next = x13> * ls(x5,x13) & null = null
         |- ls(x11,x3) * ls(x4,x13) * ls(x12,x5) * ls(x1,x9) * ls(x6,x13) * ls(x10,x7) * ls(x8,x5) * ls(x7,x13).

