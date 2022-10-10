
data tree {
    int val; 
    node children;
    }.

data node {
    tree child; 
    node next; 
    tree parent;
    }.

pred treep<n> == 
  self::tree<_,c>* c::sll<self,n-1>.

pred sll<parent,s> == 
  self=null & s=0 or 
  self::node<c,n,parent>*c::treep<s1>* n::sll<parent,s2> & s=s1+s2+1.

/*
Got base(treep):[([self], true)]


Infered base(btree):[( self::tree<_,null> & n>=1)]

Total verification time: 7.059425 second(s)
	Time spent in main process: 0.107016 second(s)
	Time spent in child processes: 6.952409 second(s)


*/