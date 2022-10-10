

data node {
  int valVAL_11;
  node nextREC_24;
}.


pred sll<n:int,sm:int,lg:int> == 
  emp&self=null & n=0 & sm<=lg or
(exists flted_16_26,qs_27,
  ql_28: self::node<qmin,q> * q::sll<flted_16_26,qs_27,ql_28>&flted_16_26+
  1=n & qmin<=qs_27 & ql_28<=lg & sm<=qmin).



/*
./s2sat benchmarks/sat/preds/sortll.slk 

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[ lg_44>=sm_43 & idx_45>=0 & idx_45=n_42]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: ((lg>=sm & n>=1) | (lg>=sm & 0=n))
!!! **astsimp.ml#2876:Predicate sll has precise invariant

 infered bases(sll)[ emp&self=null & n=0 & sm<=lg&{FLOW,(1,26)=__flow#E}[], (exists w_56,w_57: self::node<w_56,w_57>@M&1<=n & sm<=lg&
{FLOW,(1,26)=__flow#E}[])]

Stop z3... 28 invocations 
Stop Omega... 30 invocations Infer: 28 invocations; Proving: 2 invocations
SAT Count   : 42
SAT % Hit   : 50.%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 7
IMPLY % Hit : 0.%
Time(cache overhead) : 0.003071 (seconds)

0 false contexts at: ()

!!! log(small):(0.038049,78)
!!! log(big)(>0.5s)(1):(0.575757,[(imply,0.575757)])
Total verification time: 0.693098 second(s)
	Time spent in main process: 0.049012 second(s)
	Time spent in child processes: 0.644086 second(s)


*/