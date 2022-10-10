
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x_emp::RefSll_t<next = y_emp> * ls(y_emp,w_emp) * ls(w_emp,z_emp) * z_emp::RefSll_t<next = u_emp> * u_emp::RefSll_t<next = v_emp> * ls(v_emp,r_emp) * r_emp::RefSll_t<next = s_emp>
         |- ls(x_emp,s_emp).

