
ddata Refnode {
  Refnode left;
  Refnode right;
}.

pred tree<x_5:Refnode,s_6:int> ==
 emp & null = x_5 & s_6 = 0
or (exists l_7,r_8,s2_10,k: x_5::Refnode<left = l_7,right = r_8> * tree(l_7,k) * tree(r_8,s2_10) & k = s_6-s2_10-1 & 0 <= s2_10 & 0 <= k).

pred tseg<x_11:Refnode,y_12:Refnode,s_13:int> ==
 emp & s_13 = 0 & x_11 = y_12
or (exists l_14,r_15,s2_17,k: x_11::Refnode<left = l_14,right = r_15> * tree(l_14,k) * tseg(r_15,y_12,s2_17) & k = s_13-s2_17-1 & 0 <= k)
or (exists l_18,r_19,s2_21,k: x_11::Refnode<left = l_18,right = r_19> * tree(r_19,s2_21) * tseg(l_18,y_12,k) & k = s_13-s2_21-1 & 0 <= s2_21).

checkent[valid] tree(x,n) * tseg(u,v,m) * tseg(v,t,l) & 10 <= n & 20 <= m
         |- (exists a,b,c,p,q: tree(a,p) * tseg(b,c,q)).

