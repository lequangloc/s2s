
ddata Refnode {
  Refnode next;
  Refnode prev;
}.

pred dll<hd_1:Refnode,p_2:Refnode,tl_3:Refnode,n_4:Refnode,len_5:int> ==
 hd_1::Refnode<next = n_4,prev = p_2> & len_5-1 = 0 & hd_1 = tl_3
or (exists x_6,k: hd_1::Refnode<next = x_6,prev = p_2> * dll(x_6,hd_1,tl_3,n_4,k) & k = len_5-1 & 1 <= len_5-1).

                                                                 
checkent[valid] dll(x,y,z,t,k1000) & k1000 > 1 & k1000=k999 + 1 //& k1000 = 1000 & k999 = 999
         |- (exists u: z::Refnode<next = t,prev = u> * dll(x,y,u,z,k999)).
                                                                 
                                                                 /*
checkent[valid] x::Refnode<next = u1,prev = y> * dll(u1,x,z,t,k)
         |- (exists u: z::Refnode<next = t,prev = u> * dll(x,y,u,z,k)).
                                                                 */
