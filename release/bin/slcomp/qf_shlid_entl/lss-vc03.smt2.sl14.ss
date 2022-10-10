
ddata RefSll_t {
  RefSll_t next1;
  RefSll_t next2;
}.

pred lsso<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next1 = u,next2 = u> * lsso(u,out)).

checkent x_emp::RefSll_t<next1 = y_emp,next2 = y_emp> * y_emp::RefSll_t<next1 = u_emp,next2 = u_emp> * lsso(u_emp,w_emp) * w_emp::RefSll_t<next1 = z_emp,next2 = z_emp>
         |- lsso(x_emp,z_emp).

