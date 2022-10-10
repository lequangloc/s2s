
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent[valid] ls(x8,x9) * x6::RefSll_t<next = x13> * ls(x1,x4) * x11::RefSll_t<next = x1> * x5::RefSll_t<next = x6> * x2::RefSll_t<next = x1> * x3::RefSll_t<next = x13> * ls(x9,x3) * x12::RefSll_t<next = x13> * x10::RefSll_t<next = x9> * x14::RefSll_t<next = x13> * ls(x4,x12) * ls(x7,x13) * ls(x13,x5) & null = null
         |- ls(x11,x1) * ls(x2,x1) * ls(x14,x13) * ls(x8,x9) * ls(x6,x13) * ls(x7,x13) * ls(x1,x13) * ls(x10,x6).

