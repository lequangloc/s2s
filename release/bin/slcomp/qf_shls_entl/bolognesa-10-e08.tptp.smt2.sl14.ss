
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x8> * x3::RefSll_t<next = x7> * x4::RefSll_t<next = x1> * x5::RefSll_t<next = x1> * x10::RefSll_t<next = x5> * x8::RefSll_t<next = x3> * x6::RefSll_t<next = x10> * x2::RefSll_t<next = x6> * x9::RefSll_t<next = x3> * ls(x1,x6) & null = null
         |- ls(x4,x1) * ls(x2,x6) * ls(x7,x8) * ls(x1,x6) * ls(x9,x3) * ls(x6,x1) * ls(x8,x7).

