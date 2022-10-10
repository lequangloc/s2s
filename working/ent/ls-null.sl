data Sll_t {
  Sll_t next;
}.

pred ls<self, out:Sll_t> ==
 emp & self = out
or (exists u: self::Sll_t<next = u> * ls(u,out) & self != out).

checkent[valid] emp & null = null
         |- ls(null,null) * ls(null,null) * emp.