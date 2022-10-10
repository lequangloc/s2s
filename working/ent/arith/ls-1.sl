
ddata Refnode {
  Refnode next;
}.

pred ls<x_1:Refnode,y_2:Refnode,n_3:int> ==
 emp & n_3 = 0 & x_1 = y_2
or (exists u_4,k: x_1::Refnode<next = u_4> * ls(u_4,y_2,k) & k = n_3-1 & 0 <= n_3-1).

checkent[valid] ls(x,y,m) & m>2 & m=n+1
         |- (exists u: ls(x,u,n) * u::Refnode<y>).

/*
x|->u1 * ls(u1, y) |- ex u. ls(x, u) * u|->y

indicate LU

LU1
x|->y |- ex u. ls(x, u) * u|->y

RU
x|->y |- ex u. x|->y

LU2
x|->u1 * u1|->u2 * ls(u2, y) |- ex u. ls(x, u) * u|->y

RU
x|->u1 * u1|->u2 * ls(u2, y) |- ex u. x|->u1 * ls(u1, u) * u|->y

PTO-MATCH
u1|->u2 * ls(u2, y) |- ex u. ls(u1, u) * u|->y

CYC

*/
