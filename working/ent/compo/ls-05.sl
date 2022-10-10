
ddata RefSll_t {
  RefSll_t next;
}.

pred lls<in:RefSll_t,len1:int,out:RefSll_t,len2:int> ==
 emp & in = out & len1 = len2
or (exists u,len3: in::RefSll_t<next = u> * lls(u,len3,out,len2) & len1 = len3+1).


checkent[valid] lls(X,n0,Y,n1) * lls(Y,n1,Z,n2) & n0 = n1+2 & n1 = n2+1
         |- lls(X,n0,Z,n2) & n0 = n2+3.


                                                //checkent emp & n0 = n1+2 & n1 = n2+1 |- emp & n0 = n2+3.

