data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}.

/* view for red-black trees */
pred rb<n, cl, bh> == self = null & n=0 & bh = 1 & cl = 0 
	or self::node<v, 1, l, r> * l::rb<nl, 0, bhl> * r::rb<nr, 0, bhr> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 0, l, r> * l::rb<nl, _, bhl> * r::rb<nr, _, bhr> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl.

//	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/*

./s2sat benchmarks/sat/preds/rb.slk

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 

 Generate bases 

!!! **fixcalc.ml#878:invs:[]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: (((1+n)>=(2*bh) & bh>=1 & 1=cl) | ((3+n)>=(2*bh) & bh>=2 & 0=cl) | 
  (0=n & 1=bh & 0=cl))
 infered bases(rb)[ emp&self=null & n=0 & bh=1 & cl=0&{FLOW,(1,26)=__flow#E}[], (exists w_104,w_105,w_106,w_107: self::node<w_104,w_105,w_106,w_107>@M&cl=1&
{FLOW,(1,26)=__flow#E}[]), (exists w_108,w_109,w_110,w_111: self::node<w_108,w_109,w_110,w_111>@M&cl=0&
{FLOW,(1,26)=__flow#E}[])]

Stop z3... 35 invocations 
Stop Omega... 69 invocations Infer: 65 invocations; Proving: 4 invocations
SAT Count   : 199
SAT % Hit   : 84.42%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 5
IMPLY % Hit : 20.%
Time(cache overhead) : 0.005643 (seconds)

0 false contexts at: ()

!!! log(small):(0.066651,273)
Total verification time: 0.429929 second(s)
	Time spent in main process: 0.05983 second(s)
	Time spent in child processes: 0.370099 second(s)


*/