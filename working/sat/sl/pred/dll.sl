data node2 {
     node2 next;
     node2 prev;
}.

pred dll<p,n> == self=null & n=0
  or self::node2<p,q> * q::dll<self,n-1>
  .



/*
./s2sat benchmarks/sat/preds/dll.slk 

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[ idx_45>=0 & idx_45=n_44]
Predicate dll has precise base

Starting Omega.../usr/local/bin/oc
 infered bases(dll)[ emp&self=null & n=0&{FLOW,(1,26)=__flow#E}[], (exists w_50,w_51: self::node2<w_50,w_51>@M&exists(idx:0<=idx & n=idx+1)&
{FLOW,(1,26)=__flow#E}[])]

Stop z3... 25 invocations 
Stop Omega... 10 invocations Infer: 8 invocations; Proving: 2 invocations
SAT Count   : 41
SAT % Hit   : 51.21%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 5
IMPLY % Hit : 0.%
Time(cache overhead) : 0.00277 (seconds)

0 false contexts at: ()

!!! log(small):(0.020367,56)
Total verification time: 0.087394 second(s)
	Time spent in main process: 0.037794 second(s)
	Time spent in child processes: 0.0496 second(s)


*/