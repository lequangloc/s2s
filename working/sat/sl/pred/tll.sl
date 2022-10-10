
data node{
	node left;
	node right;
	node next;
}.

/* predicate for a non-empty tree with chained leaf list */
pred tll<ll,lr,n> == self::node<null,null,lr> & self = ll & n=1
  or self::node<l,r,null> * l::tll<ll,z,n1> * r::tll<z,lr,n2> & n=n1+n2+1.
//	inv self!=null;



/*
./s2sat benchmarks/sat/preds/tll.slk 

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[ idx_85>=0 & n_84>=(1+idx_85)]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: n>=1

 infered bases(tll)[ (exists w_99,w_100,w_101: self::node<w_99,w_100,w_101>@M&n=1 & self=ll&
{FLOW,(1,26)=__flow#E}[]), (exists w_102,w_103,w_104,w_105,w_106,
w_107: ll::node<w_102,w_103,w_104>@M * self::node<w_105,w_106,w_107>@M&
exists(idx:(3+(2*idx))<=n & 0<=idx)&{FLOW,(1,26)=__flow#E}[])]

Stop z3... 20 invocations 
Stop Omega... 36 invocations Infer: 34 invocations; Proving: 2 invocations
SAT Count   : 60
SAT % Hit   : 73.33%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 4
IMPLY % Hit : 0.%
Time(cache overhead) : 0.006552 (seconds)

0 false contexts at: ()

!!! log(small):(0.058813,100)
Total verification time: 0.413771 second(s)
	Time spent in main process: 0.06081 second(s)
	Time spent in child processes: 0.352961 second(s)


*/