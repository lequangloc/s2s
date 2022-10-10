data node {
     node next;
}.

pred ell<n> == self=null & n=0
     or self::node<q> * q::node<p> * p::ell<n-2>
     .

/*
../../../sleek evenll.slk --inv-baga

infered base(ell):
[([], self=null & n=0),([self], exists(idx:0<=idx & n=2+(2*idx)))]

Total verification time: 0.284017 second(s)
	Time spent in main process: 0.088372 second(s)
	Time spent in child processes: 0.195645 second(s)


*/