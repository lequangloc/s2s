
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x13> * x3::RefSll_t<next = x12> * ls(x8,x3) * ls(x7,x6) * x13::RefSll_t<next = x6> * ls(x9,x1) * ls(x2,x8) * x14::RefSll_t<next = x13> * x10::RefSll_t<next = x6> * x11::RefSll_t<next = x9> * x1::RefSll_t<next = x14> * x12::RefSll_t<next = x13> * x4::RefSll_t<next = x2> * x6::RefSll_t<next = x14> & null = null
         |- ls(x7,x6) * ls(x4,x8) * ls(x11,x9) * ls(x8,x12) * ls(x10,x6) * ls(x9,x13) * ls(x5,x13) * ls(x12,x14).

