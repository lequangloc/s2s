
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).


checkent[valid] x14::RefSll_t<next = x7> * ls(x9,x8) * x7::RefSll_t<next = x17> * ls(x8,x11) * x5::RefSll_t<next = x14> * ls(x12,x5) * x2::RefSll_t<next = x16> * ls(x16,x3) * ls(x15,x10) * x10::RefSll_t<next = x7> * x6::RefSll_t<next = x17> * x13::RefSll_t<next = x3> * ls(x17,x9) * ls(x11,x3) * ls(x4,x16) * x3::RefSll_t<next = x14> * x1::RefSll_t<next = x3> & null = null
         |- ls(x1,x3) * ls(x2,x16) * ls(x13,x3) * ls(x12,x5) * ls(x4,x16) * ls(x16,x3) * ls(x6,x17) * ls(x15,x7) * ls(x5,x7) * ls(x7,x14).


  /*

  */
