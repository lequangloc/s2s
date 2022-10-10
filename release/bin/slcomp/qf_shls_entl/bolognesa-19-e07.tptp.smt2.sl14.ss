
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x19::RefSll_t<next = x14> * ls(x12,x2) * x15::RefSll_t<next = x17> * ls(x16,x11) * ls(x10,x1) * ls(x5,x10) * x4::RefSll_t<next = x8> * x9::RefSll_t<next = x19> * ls(x17,x11) * x14::RefSll_t<next = x16> * x7::RefSll_t<next = x19> * x11::RefSll_t<next = x8> * ls(x8,x13) * x2::RefSll_t<next = x19> * ls(x1,x18) * x13::RefSll_t<next = x8> * x6::RefSll_t<next = x18> * ls(x3,x1) * x18::RefSll_t<next = x8> & null = null
         |- ls(x4,x8) * ls(x15,x17) * ls(x7,x19) * ls(x6,x18) * ls(x3,x1) * ls(x13,x8) * ls(x12,x19) * ls(x5,x10) * ls(x17,x11) * ls(x10,x8) * ls(x9,x13).

