
ddata Refnode {
  Refnode next;
}.

pred ls<x_1:Refnode,y_2:Refnode,n_3:int> ==
 emp & n_3 = 0 & x_1 = y_2
or (exists u_4,k: x_1::Refnode<next = u_4> * ls(u_4,y_2,k) & k = n_3-1 & 0 <= n_3-1).

checkent[valid] ls(x,y,k1000) & k1000 = 1000 & k800 = 800 & k200 = 200
         |- (exists u: ls(u,y,k800) * ls(x,u,k200)).

