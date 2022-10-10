ddata RefTLL_t {
  RefTLL_t left;
  RefTLL_t right;
  RefTLL_t next;
  RefTLL_t parent;
}.

pred TLL_plus<root:RefTLL_t,pra:RefTLL_t,ll:RefTLL_t,lr:RefTLL_t> ==
 root::RefTLL_t<left = null,right = null,next = lr,parent = pra> & root = ll
or (exists l,r,z: root::RefTLL_t<left = l,right = r,next = null,parent = pra> * TLL_plus(l,root,ll,z) * TLL_plus(r,root,z,lr)).


checkent[valid] a::RefTLL_t<left = l,right = r,next = null,parent = null> * TLL_plus(l,a,c,z) * TLL_plus(r,a,z,null)
         |- TLL_plus(a,null,c,null).


/*
checksat[sat] a::RefTLL_t<left = l,right = r,next = null,parent = null> * TLL_plus(l,a,c,z) * TLL_plus(r,a,z,null).
*/

/*
checksat[sat]   TLL_plus(x,parent,llll,rrrr).
*/