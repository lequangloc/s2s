
data Sll_t {
  Sll_t next;
}.

pred ls<self, out> == emp & self = out
 or (exists u: self::Sll_t<next=u> * ls(u, out) & self != out).

/*
//bolognesa-14-e08
checkent[valid]  ls(x8, x9) * x6::Sll_t<x13> *
 ls(x1, x4)
 * x11::Sll_t<x1> * x5::Sll_t<x6> * 
 x2::Sll_t<x1> * x3::Sll_t<x13> * ls(x9, x3) * x12::Sll_t<x13> * 
 x10::Sll_t<x9> * x14::Sll_t<x13> * ls(x4, x12) * ls(x7, x13) * ls(x13, x5)
    |-  ls(x11, x1) * ls(x2, x1) * ls(x14, x13) * ls(x8, x9) * ls(x6, x13) * 
 ls(x7, x13) * ls(x1, x13) * ls(x10, x6) .
*/

/*
checkent[valid]  ls(x8, x9) * x6::Sll_t<x13>  * x11::Sll_t<x1> * x5::Sll_t<x6> * 
 x2::Sll_t<x1> * x3::Sll_t<x13> * ls(x9, x3) * x12::Sll_t<x13> * 
 x10::Sll_t<x9> * x14::Sll_t<x13> * ls(x4, x12) * ls(x7, x13) * ls(x13, x5) * ls(x1, x4)
    |-  ls(x11, x1) * ls(x2, x1) * ls(x14, x13) * ls(x8, x9) * ls(x6, x13) * 
 ls(x7, x13) * ls(x1, x13) * ls(x10, x6) .
*/

/*
checkent[valid]   x10::Sll_t<x9> * ls(x9, x3) * x3::Sll_t<x13> * ls(x1, x4) * x5::Sll_t<x6> * 
   x12::Sll_t<x13> * 
  ls(x4, x12) * ls(x13, x5) * x6::Sll_t<x13>
    |-  ls(x1, x13) * ls(x10, x6) * ls(x6, x13).
*/

/*
checkent[valid]   x13::Sll_t<x5>   * ls(x1, x4) *   x12::Sll_t<x13> *   ls(x4, x12)
    |-  ls(x1, x13) * x13::Sll_t<x5>.
*/


//bolognesa-16-e05
checkent[valid]  ls(x8, x12) * x3::Sll_t<x10> * ls(x13, x5) * x14::Sll_t<x5> * ls(x5, x15) * 
 ls(x7, x16) * x11::Sll_t<x1> * x9::Sll_t<x16> * x12::Sll_t<x9> * 
 ls(x16, x3)  * x15::Sll_t<x16> * x2::Sll_t<x10> * ls(x4, x6) * 
 x10::Sll_t<x9> * x6::Sll_t<x9> * x1::Sll_t<x8> 
    |-  ls(x2, x10) * ls(x13, x5) * ls(x4, x9) * ls(x14, x5) * ls(x7, x16) * 
 ls(x11, x16) * ls(x5, x9).
