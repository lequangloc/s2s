ddata Sll_t {
  Sll_t next;
}.

pred ls<self, out> == emp &  self = out
 or (exists u: self::Sll_t<next=u> * ls(u, out) & self != out).



checkent[valid]  ls(x5, x7) * x10::Sll_t<x4> * x6::Sll_t<x9> * x7::Sll_t<x3> * 
 x3::Sll_t<x6> * x9::Sll_t<x4> * ls(x2, x4) * ls(x8, x10) * 
 x1::Sll_t<x10> * x4::Sll_t<x10> & null=null
    |-  ls(x1, x10) * ls(x5, x7) * ls(x7, x6) * ls(x6, x9) * ls(x9, x4) * 
 ls(x2, x4) * ls(x8, x4) * ls(x4, x10).


/*

x4::Sll_t<x10> * x10::Sll_t<x4> 
|- ls(x4, x10)

*/

//checkent[valid] x6::Sll_t<x9> * x9::Sll_t<x4> |- ls(x6, x9) * x9::Sll_t<x4>.
