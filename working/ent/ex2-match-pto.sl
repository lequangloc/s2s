ddata node {
  node next;
  node next2;
}.

//2 TODO
//checkent[valid] x::node<_,_> |- exists z: z::node<_,_>.

//11d
//checkent[invalid] x::node<_,_> |-  exists z: x::node<_,z> * z::node<_,_> & z=x.

checkent[valid] x::node<_,_> |- x::node<_,_>.

/*

//2
checkent[valid] x::node<_,_> |- exists z: z::node<_,_>.

//3
checkent[valid]  x::node<u1, u2> * u1::node<null, null> |-  exists u,u3: x::node<u,u3> * u::node<_,null>.

//4
checkent[valid] exists u1: x::node<u1, u2> * u1::node<null, null> |-  exists u,u3: x::node<u,u3> * u::node<_,null>.

//5
checkent[valid] exists u1: x::node<u1, u2> |-  exists u,u3: x::node<u,u3>.

//6
checkent[invalid] exists u1: x::node<u1, u2> |-  x::node<u,u3>.

//7
checkent[valid] exists u1: x::node<u1, u2> & u2=u3 |-  x::node<u,u3>.

//8
checkent[valid] x::node<u> |- exists z: x::node<z>.

//9
checkent[invalid] x::node<y> |- x::node<z>.

//10
//need footprint for Elt.eval
checkent[valid] x::node<u,_> * u::node<null,_>  |- exists z: x::node<z,_> * z::node<_,_> & x!=z.

//11a
checkent[valid] x::node<_,_> |- x::node<_,_> & x!=null.

//11b
checkent[invalid] x::node<_,_> |- x::node<_,_> & x=null.

//11c
checkent[invalid] x::node<_,_> |- x::node<_,_> * x::node<_,_> .


*/
