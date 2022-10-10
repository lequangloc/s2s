
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x5::RefSll_t<next = x10> * ls(x9,x7) * x2::RefSll_t<next = x7> * x4::RefSll_t<next = x7> * x6::RefSll_t<next = x4> * x7::RefSll_t<next = x3> * x1::RefSll_t<next = x2> * x10::RefSll_t<next = x1> * x8::RefSll_t<next = x4> * x3::RefSll_t<next = x5> & null = null
         |- ls(x3,x5) * ls(x8,x4) * ls(x9,x7) * ls(x6,x7) * ls(x5,x3).

