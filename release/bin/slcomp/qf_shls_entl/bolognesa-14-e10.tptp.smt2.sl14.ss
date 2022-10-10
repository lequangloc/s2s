
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x14::RefSll_t<next = x4> * x10::RefSll_t<next = x11> * ls(x8,x12) * ls(x13,x4) * x1::RefSll_t<next = x7> * ls(x5,x1) * x6::RefSll_t<next = x4> * ls(x4,x13) * x2::RefSll_t<next = x3> * x3::RefSll_t<next = x1> * x12::RefSll_t<next = x14> * ls(x7,x3) * ls(x11,x12) * ls(x9,x4) & null = null
         |- ls(x6,x4) * ls(x2,x3) * ls(x13,x4) * ls(x9,x4) * ls(x10,x11) * ls(x3,x1) * ls(x5,x3) * ls(x8,x12) * ls(x11,x13).

