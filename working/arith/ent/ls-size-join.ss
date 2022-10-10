ddata node {
     node next;
}.


pred ls<x,y,i> == emp & x = y & i=0
  or exists u,i1: x::node<u> * ls(u,y,i1) & i=i1+1.


  //OK
  //  checkent[valid]  ls(x,y,m) * ls(y,null,n) |- ls(x,null,m+n).

  //OK
  // checkent[valid]  ls(x,y,m) * ls(y,null,n) & k=m+2 & n=2 |- ls(x,null,k) & k>=2.

  //TODO
    checkent[valid]  ls(x,y,m) * ls(y,null,n) & k=m+n |- ls(x,null,k).
  //checkent m=(1+i1_46) &  k=(n+m) &  k=(1+i1_71) |- i1_71 = n + i1_46.

  /*
  checkent (exists i1_112,i1_79,i1_46: emp & n=(1+i1_164) & u_139=y & i1_112=0 & i1_79=(1+i1_112) & i1_46=(1+i1_79) & m=(1+i1_46) & flted_163=null & k=(n+m)) //n=i1_137
   |- (exists i1_137,i1_104,i1_71: emp & i1_137=(1+i1_164) & i1_104=(1+i1_137) & i1_71=(1+i1_104) & k=(1+i1_71) & flted_163=null).
  */

