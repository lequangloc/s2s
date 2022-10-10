data node2 {
     node2 left;
     node2 right;
}.

pred btree<n> == self=null & n=0
     or self::node2<l,r> * l::btree<n1> * r::btree<n2> & n=n1+n2+1
     .

/*
../../../sleek bt.slk --inv-baga

Infered base(btree):[([], self=null & n=0),([self], 1<=n)]

Total verification time: 1.41557 second(s)
	Time spent in main process: 0.103176 second(s)
	Time spent in child processes: 1.312394 second(s)

*/