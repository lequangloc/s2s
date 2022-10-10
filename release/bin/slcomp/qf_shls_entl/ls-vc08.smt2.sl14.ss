
ddata RefSll_t {
  RefSll_t next;
}.

pred ls<in:RefSll_t,out:RefSll_t> ==
 emp & in = out
or (exists u: in::RefSll_t<next = u> * ls(u,out) & in != out).

checkent ls(x_emp,y_emp) * ls(y_emp,z_emp) & z_emp = null
         |- ls(x_emp,z_emp).

