
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
  int val;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t, ma:int, mi:int> ==
 emp & fr = nx & bk = pr & ma=mi
  or (exists u,m1: fr::RefDll_t<next = u,prev = pr, val = ma> * dll(u,bk,fr,nx, m1, mi) & fr != nx & ma>m1+1).

