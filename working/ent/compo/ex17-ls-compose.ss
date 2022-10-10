
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

pred lseg<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * lseg(u,out)).

  /*
    (ls(in, b), ls(in, out)) and out is dangling  ==> (frame: (ls(in, b), RHS: ls(b, out), pure, assumptions)

 [(in,out); (src,tag); (u)] [b; tar'] ==>

dangling condition:
 - out is either null or points-to
 - in != out
   */

  //1a.
  // checkent[valid] lseg(x, y) |- lseg(x, y).
  // not -compo: unfold left, unfold right, match pto, cyclic
  // compo: compositional rule, RBase
  
  //1b
  //  checkent[valid] ls(x, y) |- ls(x, y).

//1. do
  checkent[valid] lseg(x, y) * lseg(y, null) |- lseg(x, null).
//  checkent[valid] ls(x, y) * ls(y, null) |- ls(x, null).

  /*
//2. do: check z in fp and the LHS
 checkent[valid] ls(x, y) * ls(y, z) * z::RefSll_t<null> |- ls(x, z) * z::RefSll_t<null>.
  */

  /*
  //3 do NOT
checkent[invalid] ls(x, y) * ls(y, z) |- ls(x, z) .
  */
