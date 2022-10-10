

/*
checkent[valid] emp & flted_126=null & flted_159=null & flted_185=null & x1!=x1_1 & x1!=x1_2 & x1!=x1_3 & x1!=x2 & x1!=x2_1 & x1!=x2_2 & x1_1!=x1_2 & x1_1!=x1_3 & x1_1!=x2 & x1_1!=x2_1 & x1_1!=x2_2 & x1_2!=x1_3 & x1_2!=x2 & x1_2!=x2_1 & x1_2!=x2_2 & x1_3!=x2 & x1_3!=x2_1 & x1_3!=x2_2 & x2!=x2_1 & x2!=x2_2 & x2_1!=x2_2 & x1!=null & x1_1!=null & x1_2!=null & x1_3!=null & x2!=null & x2_1!=null & x2_2!=null
 |-
 emp & x2_2!=flted_185 & x2_1!=flted_185 & x2!=flted_159 & flted_126=flted_185 & x1_3!=flted_185 & x1_2!=flted_185 & x1_1!=flted_185 & x1!=flted_159 & flted_159=null & flted_185=null.
*/

/*
checkent[valid] emp & flted_126=null & flted_159=null & flted_185=null & x1!=x1_1 & x1!=x1_2 & x1!=x1_3 & x1!=x2 & x1!=x2_1 & x1!=x2_2 & x1_1!=x1_2 & x1_1!=x1_3 & x1_1!=x2 & x1_1!=x2_1 & x1_1!=x2_2 & x1_2!=x1_3 & x1_2!=x2 & x1_2!=x2_1 & x1_2!=x2_2 & x1_3!=x2 & x1_3!=x2_1 & x1_3!=x2_2 & x2!=x2_1 & x2!=x2_2 & x2_1!=x2_2 & x1!=null & x1_1!=null & x1_2!=null & x1_3!=null & x2!=null & x2_1!=null & x2_2!=null
 |-
 emp  & x2_2!=flted_185 
 & x2_1!=flted_185
 & x2!=flted_159
// & flted_126=flted_185
 & x1_3!=flted_185 & x1_2!=flted_185 & x1_1!=flted_185 & x1!=flted_159 & flted_159=null & flted_185=null.
*/

//checkent[valid] emp & flted_126=null & flted_185=null |- emp  & flted_126=flted_185.


checkent[valid] emp & u_71=y_emp & u_emp=w_emp & w_emp!=y_emp & u_emp!=x_emp & flted_50=null &
                 x_emp!=w_emp & x_emp!=z_emp & y_emp!=z_emp &
                   x_emp != null & w_emp != null & y_emp != null &
                   x_emp != w_emp & w_emp != y_emp & w_emp != y_emp
   |- emp &// y_emp=u_71 & u_71!=z_emp & y_emp!=w_emp & 
      w_emp!=z_emp //& // y_emp!=x_emp & x_emp!=z_emp
   // &
   // y_emp!=flted_50 & flted_50=null
   // & w_emp=u_emp
  .

/*
emp & u_71=y_emp && u_emp=w_emp && w_emp!=y_emp && u_emp!=x_emp && flted_50=null && x_emp!=w_emp && x_emp!=z_emp && y_emp!=z_emp
   |= emp & y_emp=u_71 && u_71!=z_emp && y_emp!=w_emp && w_emp!=z_emp && y_emp!=x_emp && x_emp!=z_emp && y_emp!=flted_50 && flted_50=null && w_emp=u_emp
footprint == x_emp::Dll_t<w_emp,flted_50> * w_emp::Dll_t<u_71,x_emp> * y_emp::Dll_t<z_emp,u_emp>

*/