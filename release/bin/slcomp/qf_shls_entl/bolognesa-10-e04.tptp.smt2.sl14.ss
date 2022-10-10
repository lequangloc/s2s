
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x3::RefSll_t<next = x7> * x1::RefSll_t<next = x4> * x4::RefSll_t<next = x8> * ls(x8,x3) * x2::RefSll_t<next = x7> * x5::RefSll_t<next = x3> * x6::RefSll_t<next = x8> * ls(x9,x4) * x10::RefSll_t<next = x7> * ls(x7,x9) & null = null
         |- ls(x2,x7) * ls(x6,x8) * ls(x5,x3) * ls(x10,x7) * ls(x9,x4) * ls(x1,x4) * ls(x4,x9).

