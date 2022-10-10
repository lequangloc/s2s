data node3 {
     node3 left;
     node3 right;
     node3 next;
}.

pred tll<ll,lr> == self::node3<null,null,lr> & self=ll
     or self::node3<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
     .

/*
infered base (tll):[([self], self=ll),([ll,self], true)]
Total verification time: 0.144528 second(s)
	Time spent in main process: 0.090153 second(s)
	Time spent in child processes: 0.054375 second(s)


*/