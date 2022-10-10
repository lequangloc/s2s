
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred dll<fr:RefDll_t,bk:RefDll_t,pr:RefDll_t,nx:RefDll_t> ==
 emp & fr = nx & bk = pr
or (exists u: fr::RefDll_t<next = u,prev = pr> * dll(u,bk,fr,nx)).


checkent[valid] dll(x, w , null, t) |- dll(x,w,null,t).

  /*
use composition rule not matching
   */
