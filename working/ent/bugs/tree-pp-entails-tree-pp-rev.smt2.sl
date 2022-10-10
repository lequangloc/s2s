
data TPP_t {
  TPP_t left;
  TPP_t right;
  TPP_t parent;
}.

pred TPP_plus<x:TPP_t,back:TPP_t> ==
 x::TPP_t<left = null,right = null,parent = back>
or (exists y,z: x::TPP_t<left = y,right = z,parent = back> * TPP_plus(y,x) * TPP_plus(z,x)).

pred TPP_aux<x:TPP_t,down:TPP_t,top:TPP_t,b:TPP_t> ==
 (exists up,right: x::TPP_t<left = down,right = right,parent = up> * TPP_plus(right,x) * TPP_aux(up,x,top,b))
or (exists up,left: x::TPP_t<left = left,right = down,parent = up> * TPP_plus(left,x) * TPP_aux(up,x,top,b))
or (exists right: x::TPP_t<left = down,right = right,parent = b> * TPP_plus(right,x) & x = top)
or (exists left: x::TPP_t<left = left,right = down,parent = b> * TPP_plus(left,x) & x = top).

pred TPP_plus_rev<top:TPP_t,b:TPP_t> ==
 top::TPP_t<left = null,right = null,parent = b>
or (exists x,up: x::TPP_t<left = null,right = null,parent = up> * TPP_aux(up,x,top,b)).

checkent[valid] TPP_plus(x,y)
         |- TPP_plus_rev(x,y).

