ddata Refnode {
  Refnode next;
  Refnode prev;
}.

pred dll<hd_1:Refnode,p_2:Refnode,tl_3:Refnode,n_4:Refnode,l_5:int> ==
 hd_1::Refnode<next = n_4,prev = p_2> & l_5+(-1) = 0 & hd_1 = tl_3
or (exists x_6,k: hd_1::Refnode<next = x_6,prev = p_2> * dll(x_6,hd_1,tl_3,n_4,k) & k = l_5-1 & 1 <= l_5-1).

pred dllnull<hd_7:Refnode,p_8:Refnode,l_9:int> ==
 hd_7::Refnode<next = null,prev = p_8> & l_9-1 = 0
or (exists x_10,k: hd_7::Refnode<next = x_10,prev = p_8> * dllnull(x_10,hd_7,k) & k = l_9-1 & 1 <= l_9-1).
