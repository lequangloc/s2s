/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}.


pred pq<n, mx> == self = null & n = 0 & mx = 0 
	or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
	& n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) . //0 <= n1 - n2 & n1 - n2 <= 1

/*

./s2sat benchmarks/sat/preds/heaps.slk

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: ((n>=1 & mx>=0) | (0=n & 0=mx))
 infered bases(pq)[ emp&self=null & n=0 & mx=0&{FLOW,(1,26)=__flow#E}[], (exists w_72,w_73,w_74,w_75,w_76: self::node<w_72,w_73,w_74,w_75,w_76>@M&
1<=n & 0<=mx&{FLOW,(1,26)=__flow#E}[])]

Stop z3... 29 invocations 
Stop Omega... 38 invocations Infer: 36 invocations; Proving: 2 invocations
SAT Count   : 71
SAT % Hit   : 63.38%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 4
IMPLY % Hit : 25.%
Time(cache overhead) : 0.003187 (seconds)

0 false contexts at: ()

!!! log(small):(0.072644,113)
Total verification time: 0.198975 second(s)
	Time spent in main process: 0.051517 second(s)
	Time spent in child processes: 0.147458 second(s)



*/