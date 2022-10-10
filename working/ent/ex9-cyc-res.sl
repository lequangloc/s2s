

data node {
  node next;
}.


pred ls<x,y> == emp & x = y
  or exists u: x::node<u> * ls(u,y).

pred rls<x,y> == emp & x = y
  or exists u: rls(x,u) *  u::node<y>.


//2a: done
//checkent[valid]  x::node<u> * rls(u,y) |- rls(x,y) .


//3
checkent[valid] ls(x,y) |- rls(x,y) .

/*
//1 done
checkent[valid] rls(x,y) |- ls(x,y) .

//2a: done
checkent[valid]  x::node<u> * rls(u,y) |- rls(x,y) .


//2b: done
checkent[valid] rls(x,u) * u::node<y> |- rls(x,y) .

//3
checkent[valid] ls(x,y) |- rls(x,y) .

//4
checkent (exists u_34: x::node<u_34> * rls(u_34,y) & true)
   |- (exists u_42: rls(x,u_42) * u_42::node<y> & true).


//5
checkent[valid] ls(x, u)* u::node<y> |- ls(x,y) .
*/
