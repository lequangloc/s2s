
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent x_emp::RefSll_t<next = y_emp> * ls(y_emp,w_emp) * w_emp::RefSll_t<next = z_emp>
         |- ls(x_emp,z_emp).

