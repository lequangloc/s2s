data Sll_t {
  Sll_t next;
}.

pred ls<self, out> == emp & self = out
 or (exists u: self::Sll_t<next=u> * ls(u, out) & self != out).




//pto
checkent[valid]   x13::Sll_t<x5>   * ls(x1, x4) *   x12::Sll_t<x13> *   ls(x4, x12)
    |-  ls(x1, x13) * x13::Sll_t<x5>.


/*
//null
checkent[valid]    ls(x1, x4) *   x12::Sll_t<x13> *   ls(x4, x12) & x13=null
    |-  ls(x1, x13) .
*/

/*
//pred
checkent[invalid]   ls(x13,x5)   * ls(x1, x4) *   x12::Sll_t<x13> *   ls(x4, x12)
    |-  ls(x1, x13) * ls(x13,x5).
*/