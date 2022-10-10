
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x7::RefSll_t<next = x1> * ls(x4,x9) * ls(x9,x2) * x10::RefSll_t<next = x9> * x6::RefSll_t<next = x2> * ls(x2,x8) * x1::RefSll_t<next = x5> * x5::RefSll_t<next = x8> * x3::RefSll_t<next = x6> * x8::RefSll_t<next = x3> & null = null
         |- ls(x10,x9) * ls(x7,x8) * ls(x4,x2) * ls(x2,x8) * ls(x8,x2).

