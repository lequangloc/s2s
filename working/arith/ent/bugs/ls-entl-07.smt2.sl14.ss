
ddata RefSll_t {
  RefSll_t next;
  int data;
}.

pred lsls<in:RefSll_t,dt1:int,len1:int,out:RefSll_t,dt2:int,len2:int> ==
 emp & in = out & dt1 = dt2 & len1 = len2
  or (exists u,dt3,len3: in::RefSll_t<next = u,data = dt1> * lsls(u,dt3,len3,out,dt2,len2) & dt1 < dt3 //+ 0
 & len1 = len3+1).

  checkent[valid] lsls(X,d1,n1,Y,d2,n2) * Y::RefSll_t<next = Z,data = d3> * lsls(Z,d4,n3,U,d5,n4) & d1 != d2 & d2 = d3 & n3 = n4+2 & n2 = n3+1 & d3 < d4
     |- lsls(X,d1,n1,U,d5,n4) .//& d1 < d5 & n1 > n4+3.

