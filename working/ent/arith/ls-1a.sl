
ddata Refnode {
  Refnode next;
}.

pred ls<x_1:Refnode,y_2:Refnode,n_3:int> ==
 emp & n_3 = 0 & x_1 = y_2
or (exists u_4,k: x_1::Refnode<next = u_4> * ls(u_4,y_2,k) & k = n_3-1 & 0 <= n_3-1).

checkent[valid] ls(x,y,m) & m>1 & m=n+2
         |- (exists u1,u2: x::Refnode<u1> * ls(u1,u2,n) * u2::Refnode<y>).

