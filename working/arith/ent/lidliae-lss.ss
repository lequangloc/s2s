
ddata RefSll_t {
  RefSll_t next;
}.

pred lls<in:RefSll_t,len1:int,out:RefSll_t,len2:int> ==
 emp & in = out & len1 = len2
or (exists u,len3: in::RefSll_t<next = u> * lls(u,len3,out,len2) & len1 = len3+1).
