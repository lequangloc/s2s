
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x8,x12) * x12::RefSll_t<next = x2> * ls(x11,x9) * ls(x6,x10) * x2::RefSll_t<next = x6> * ls(x5,x9) * x3::RefSll_t<next = x4> * ls(x4,x8) * x1::RefSll_t<next = x6> * x10::RefSll_t<next = x1> * x9::RefSll_t<next = x7> * ls(x7,x4) & null = null
         |- ls(x11,x9) * ls(x1,x6) * ls(x3,x4) * ls(x5,x8) * ls(x8,x1).

