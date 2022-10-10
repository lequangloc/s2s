
ddata Refnode {
  Refnode next;
  int val;
}.

pred sls<x_1:Refnode,y_2:Refnode,l_3:int,u_4:int> ==
 x_1::Refnode<next = y_2,val = l_3> & l_3 = u_4
or (exists t_5,a_6: x_1::Refnode<next = t_5,val = l_3> * sls(t_5,y_2,a_6,u_4) & a_6 <= u_4 & l_3 <= a_6).

checkent[valid] sls(x,y,l,u) & l < u
         |- (exists t,r: t::Refnode<next = y,val = u> * sls(x,t,l,r) & r <= u).

