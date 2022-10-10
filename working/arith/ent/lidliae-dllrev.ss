ddata Refnode {
  Refnode next;
  Refnode prev;
}.

pred dll<hd_1:Refnode,p_2:Refnode,tl_3:Refnode,n_4:Refnode,len_5:int> ==
 hd_1::Refnode<next = n_4,prev = p_2> & len_5+(-1) = 0 & hd_1 = tl_3
or (exists x_6,k: hd_1::Refnode<next = x_6,prev = p_2> * dll(x_6,hd_1,tl_3,n_4,k) & k = len_5+(-1) & 1 <= len_5+(-1)).

pred dll_rev<hd_7:Refnode,p_8:Refnode,tl_9:Refnode,n_10:Refnode,len_11:int> ==
 hd_7::Refnode<next = n_10,prev = p_8> & len_11+(-1) = 0 & hd_7 = tl_9
or (exists x_12,k: tl_9::Refnode<next = n_10,prev = x_12> * dll_rev(hd_7,p_8,x_12,tl_9,k) & k = len_11+(-1) & 1 <= len_11+(-1)).
