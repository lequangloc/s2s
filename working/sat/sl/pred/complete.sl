data node2 {
	int  val;
	node2 left;
	node2 right; 
}.

pred complete<n, nmin> == self = null & n = 0 & nmin = 0
	or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-2, nmin2> & nmin = min(nmin1, nmin2) + 1
	or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-1, nmin2> & nmin = min(nmin1, nmin2) + 1.




/*
./s2sat benchmarks/sat/preds/complete.slk

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[ idx_84>=nmin_83 & (2*nmin_83)>=idx_84 & idx_84=n_82]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: ((n>=nmin & n>=1) | (0=n & 0=nmin))
!!! **astsimp.ml#2879:Predicate complete has over invariant

 infered bases(complete)[ emp&self=null & n=0 & nmin=0&{FLOW,(1,26)=__flow#E}[], (exists w_111,w_112,w_113: self::node2<w_111,w_112,w_113>@M&
exists(idx:idx<=((2*nmin)-2) & (nmin-1)<=idx & n=idx+1)&
{FLOW,(1,26)=__flow#E}[])]

Stop z3... 32 invocations 
Stop Omega... 69 invocations Infer: 65 invocations; Proving: 4 invocations
SAT Count   : 141
SAT % Hit   : 81.56%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 7
IMPLY % Hit : 14.28%
Time(cache overhead) : 0.005805 (seconds)

0 false contexts at: ()

!!! log(small):(0.066613,216)
!!! log(big)(>0.5s)(1):(1.767935,[(imply,1.767935)])
Total verification time: 1.92959 second(s)
	Time spent in main process: 0.064182 second(s)
	Time spent in child processes: 1.865408 second(s)



*/