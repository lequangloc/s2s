ddata RefTLL_t {
  RefTLL_t left;
  RefTLL_t right;
}.

pred bt<root:RefTLL_t> ==
 root::RefTLL_t<left = null,right = null>
or (exists l,r,z: root::RefTLL_t<left = l,right = r> * bt(l) * bt(r)).


checksat[sat]   bt(x).