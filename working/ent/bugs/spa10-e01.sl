data Sll_t {
  Sll_t next;
}.

pred ls<self, out> == emp & self = out
 or (exists u: self::Sll_t<next=u> * ls(u, out) & self != out).


checkent[valid]  ls(x5, x7) * ls(x2, x5) * ls(x2, x10) * ls(x2, x1) * ls(x9, x1) * 
 ls(x7, x6) * ls(x3, x10) * ls(x6, x9) & 
x2!=x7 & x2!=x3 & x2!=x6 & x7!=x10 & x3!=x8 & x4!=x9 & x4!=x7 & x4!=x8 & 
x1!=x10 & x1!=x7 & x1!=x6
    |- false.


/*
checksat[unsat] emp & x6=x9 & x3=x10 & x7=x6 & x9=x1 & x2=x1 & x2=x10 & x2=x5 & x5=x7 & x2!=x7 & x2!=x3 & x2!=x6 & x7!=x10 & x3!=x8 & x4!=x9 & x4!=x7 & x4!=x8 & x1!=x10 & x1!=x7 & x1!=x6.
*/

/*
checkent[invalid]  ls(x5, x7) * ls(x7, x5)  & 
x5!=x7 
    |- false.
*/
/*
checksat[unsat]  ls(x5, x7) * ls(x2, x5) * ls(x2, x10) * ls(x2, x1) * ls(x9, x1) * 
 ls(x7, x6) * ls(x3, x10) * ls(x6, x9) & 
x2!=x7 & x2!=x3 & x2!=x6 & x7!=x10 & x3!=x8 & x4!=x9 & x4!=x7 & x4!=x8 & 
x1!=x10 & x1!=x7 & x1!=x6.
*/