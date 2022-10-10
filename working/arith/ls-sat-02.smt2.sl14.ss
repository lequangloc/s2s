
data RefSll_t {
    RefSll_t next;
}.

pred lls<in,len1,out,len2> == 
    (emp & in=out & len1=len2)
     or (exists u,len3: in::RefSll_t<next=u> * lls(u,len3,out,len2) & len1=len3+1).


checksat[unsat] y_emp::RefSll_t<next=z_emp> * lls(y_emp,n1,w_emp,n2) & n1>n2.
