
ddata RefSll2h_t {
  RefSll2h_t next;
  RefSll2h_t head;
}.

pred sllpf<in:RefSll2h_t,out:RefSll2h_t,head:RefSll2h_t> ==
 emp & in = out
or (exists u: in::RefSll2h_t<next = u,head = head> * sllpf(u,out,head)).

pred sllh<in:RefSll2h_t,out:RefSll2h_t> ==
sllpf(in,out,in).

checkent[invalid] sllh(x0,null)
         |- false.

