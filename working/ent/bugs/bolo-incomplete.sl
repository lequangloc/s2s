

data Sll_t {
  Sll_t next;
}.

pred ls<self, out> == emp & self = out
 or (exists u: self::Sll_t<next=u> * ls(u, out) & self != out).

/*
//12-e01
checkent[valid]  x10::Sll_t<x6> * x2::Sll_t<x1> * x8::Sll_t<x5> * x4::Sll_t<x7> * 
 x1::Sll_t<x6> * x9::Sll_t<x3> * x6::Sll_t<x4> * ls(x12, x8) * 
 x5::Sll_t<x1> * x7::Sll_t<x6> * x3::Sll_t<x5> * ls(x11, x8)
    |-  ls(x10, x6) * ls(x12, x8) * ls(x11, x5) * ls(x9, x5) * ls(x5, x1) * 
 ls(x2, x4) * ls(x4, x6).
*/

/*
//12-e08
checkent[valid]  ls(x8, x7) * x3::Sll_t<x12> * x6::Sll_t<x9> * ls(x2, x11) * ls(x4, x6) * 
 ls(x9, x12) * x12::Sll_t<x6> * x5::Sll_t<x4> * x10::Sll_t<x8> * 
 x7::Sll_t<x11> * x1::Sll_t<x6> * x11::Sll_t<x6>
    |-  ls(x1, x6) * ls(x10, x8) * ls(x8, x7) * ls(x7, x11) * ls(x3, x6) * 
 ls(x2, x6) * ls(x5, x12).
*/


//12-e09

checkent[valid]  ls(x8, x12) * x12::Sll_t<x2> * ls(x11, x9) * ls(x6, x10) * x2::Sll_t<x6> * 
 ls(x5, x9) * x3::Sll_t<x4> * ls(x4, x8) * x1::Sll_t<x6> * x10::Sll_t<x1> * 
 x9::Sll_t<x7> * ls(x7, x4)
    |-  ls(x11, x9) * ls(x1, x6) * ls(x3, x4) * ls(x5, x8) * ls(x8, x1).


/*
checkent[valid]  ls(x8, x12) * x12::Sll_t<x2>  * ls(x6, x10) * x2::Sll_t<x6> * 
    x1::Sll_t<x6> * x10::Sll_t<x1>
    |-   ls(x1, x6) * ls(x8, x1).

*/
/*
checkent[invalid]  ls(x5, x9)  * x9::Sll_t<x7> * ls(x7, x4) * ls(x4, x8)
    |-   ls(x5, x8) .
*/

/*
checkent[valid]  ls(x8, x12) * x12::Sll_t<x2>  * ls(x6, x10) * x2::Sll_t<x6> * 
    x1::Sll_t<x6> * x10::Sll_t<x1>
*ls(x5, x9)  * x9::Sll_t<x7> * ls(x7, x4) * ls(x4, x8)
*ls(x11, x9)
* x3::Sll_t<x4>
    |-   ls(x1, x6) * ls(x8, x1)
*ls(x5, x8)
*ls(x11, x9)
* ls(x3, x4)
.
*/
