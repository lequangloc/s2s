ddata RefTLL_t {
  RefTLL_t left;
  RefTLL_t right;
  RefTLL_t parent;
}.

pred bt<root:RefTLL_t,pra:RefTLL_t> ==
 root::RefTLL_t<left = null,right = null,parent = pra>
or (exists l,r,z: root::RefTLL_t<left = l,right = r,parent = pra> * bt(l,root) * bt(r,root)).


checksat[sat]   bt(x,parent).