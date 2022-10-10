
ddata Refnode {
  Refnode next;
  int val;
}.

pred sls<x_1:Refnode,y_2:Refnode,l_3:int,u_4:int> ==
 x_1::Refnode<next = y_2,val = l_3> & l_3 = u_4
or (exists t_5,a_6: x_1::Refnode<next = t_5,val = l_3> * sls(t_5,y_2,a_6,u_4) & 0 <= u_4-a_6 & l_3 <= a_6).

checkent[valid] sls(x,y,k1,k100) * sls(y,z,k200,k300) & k1 = 1 & k100 = 100 & k200 = 200 & k300 = 300
         |- sls(x,z,k1,k300).

