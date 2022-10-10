data node2 {
     node2 left;
     node2 right;
}.

pred avl<n,h> == self=null & n=0 & h=0
     or self::node2<l,r> * l::avl<n1,h1> * r::avl<n2,h2> & n=n1+n2+1 & h=max(h1,h2)+1 & -1<=h1-h2<=1
     .

/*
 ./s2sat benchmarks/sat/preds/avl.slk 

!!! **tpdispatcher.ml#492:init_tp by default: 
!!! **tpdispatcher.ml#391:set_tp z3Starting z3... 
 Generate bases 

!!! **fixcalc.ml#878:invs:[ idx_55>=0 & h_54>=idx_55 & n_53>=h_54]
Starting Omega.../usr/local/bin/oc
!!! **fixcalc.ml#514:result: ((n>=0 & h>=0) | (2>=h & h=n))
 infered bases(avl)[ emp&self=null & n=0 & h=0&{FLOW,(1,26)=__flow#E}[], (exists w_73,w_74: self::node2<w_73,w_74>@M&
exists(idx:(idx+h)<=n & idx<h & 0<=idx) & (2*h)<=(2+n)&
{FLOW,(1,26)=__flow#E}[])]

Stop z3... 24 invocations 
Stop Omega... 32 invocations Infer: 30 invocations; Proving: 2 invocations
SAT Count   : 62
SAT % Hit   : 70.96%

SAT : 0
UNSAT : 0
UNKNOWN : 0

IMPLY Count : 7
IMPLY % Hit : 14.28%
Time(cache overhead) : 0.003601 (seconds)

0 false contexts at: ()

!!! log(small):(0.06751,101)
Total verification time: 0.474331 second(s)
	Time spent in main process: 0.044868 second(s)
	Time spent in child processes: 0.429463 second(s)

*/