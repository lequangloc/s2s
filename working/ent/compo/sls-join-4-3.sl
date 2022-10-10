
ddata Refnode {
  Refnode next;
  int val;
}.

pred sls<x_1:Refnode,y_2:Refnode,l_3:int,u_4:int> ==
 x_1::Refnode<next = y_2,val = l_3> & l_3 = u_4
or (exists t_5,a_6: x_1::Refnode<next = t_5,val = l_3> * sls(t_5,y_2,a_6,u_4) & 0 <= u_4-a_6 & l_3 <= a_6).

checkent[valid] sls(t,w,l4,u4) * sls(x,y,l1,u1) * sls(y,z,l2,u2) * sls(z,t,l3,u3) & u1 <= l2 & u2 <= l3 & u3 <= l4
         |- sls(x,w,l1,u3).

