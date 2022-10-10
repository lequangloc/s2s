        
ddata Refnode {
  Refnode next;
  int val;
}.

pred ls<x_1:Refnode,y_2:Refnode,l_3:int,u_4:int> ==
 x_1::Refnode<next = y_2,val = l_3> & l_3 = u_4
or (exists t_5,a_6: x_1::Refnode<next = t_5,val = l_3> * ls(t_5,y_2,a_6,u_4) & a_6 <= u_4 & l_3 <= a_6).


checkent[valid] ls(x,y,l1,u1) * ls(y,z,l2,u2) & u1 <= l2
         |- ls(x,z,l1,u2).

