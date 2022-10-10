data node {
     node next;
}.

pred sll<n> == self=null & n=0
     or self::node<q> * q::sll<n-1>
     .

/*
../../../s2sat sll.slk --inv-baga

infered base (sll):
[([], self=null & n=0),([self], exists(idx:0<=idx & n=idx+1))]

Total verification time: 0.154085 second(s)
	Time spent in main process: 0.087183 second(s)
	Time spent in child processes: 0.066902 second(s)
*/