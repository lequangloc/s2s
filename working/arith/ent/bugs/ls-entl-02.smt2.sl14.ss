
ddata RefSll_t {
  RefSll_t next;
  int data;
}.

pred sls<in:RefSll_t,dt1:int,out:RefSll_t,dt2:int> ==
 emp & in = out & dt1 = dt2
or (exists u,dt3: in::RefSll_t<next = u,data = dt1> * sls(u,dt3,out,dt2) & dt1 > dt3+1).

checkent[invalid] sls(X,a,Y,b0) * sls(Y,b1,Z,c) & a > b0 & b1 > c
         |- sls(X,a,Z,c) & a > c+3.
