ddata node {
  node next;
}.


pred ls<x:node,y:node,n:int> ==  x=y & n=0
  or (exists u: x::node<u> * ls(u,y,n-1)).



pred lsrev<x,y,n> == x=y & n=0
  or (exists u: u::node<y> * lsrev(x,u,n-1)).


checksat[unsat] lsrev(x,z,n) & n<0.


checksat[unsat] ls(x,z,n) & n<0.

// expect: sat
checksat[sat] ls(x,z,6).
// return unknown: ??

                        
// expect: sat
checksat[sat] lsrev(x,z,0).
// return unknown: ??


// expect: sat
checksat[sat] ls(x,z,1).
// return sat: OK



// expect: sat
checksat[sat] lsrev(x,z,1).
// return sat: OK


// expect: sat
checksat[sat] ls(x,z,2).
// return unsat: UNSOUND

// expect: sat
checksat[sat] lsrev(x,z,2).
// return unsat: UNSOUND

// expect: sat
checksat[sat] ls(x,z,3).
// return unsat: UNSOUND

// expect: sat
checksat[sat] lsrev(x,z,33333).
// return unsat: UNSOUND


