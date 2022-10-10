data mtree {
     int val;
     mnode next;
}.

data mnode {
     mtree child;
     mnode prev;
     mnode next;
     mtree parent;
}.

pred dll<b,p> == self=null
         or nl::dll<l,p> * self::mnode<cl,b,nl,p> * cl::mtree<v,c> * c::dll<null,cl>
         .

pred treep<> == self::mtree<v,c> * c::dll<null,t>.

/*
precise
infered base(treep):[([self], true)]

Total verification time: 0.183858 second(s)
	Time spent in main process: 0.099045 second(s)
	Time spent in child processes: 0.084813 second(s)


*/