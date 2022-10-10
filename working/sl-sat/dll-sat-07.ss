
ddata RefDll_t {
  RefDll_t next;
  RefDll_t prev;
}.

pred ldll<E:RefDll_t,P:RefDll_t,len1:int,F:RefDll_t,L:RefDll_t,len2:int> ==
 emp & E = F & P = L & len1 = len2
or (exists u,len3: E::RefDll_t<next = u,prev = P> * ldll(u,E,len3,F,L,len2) & len1 = len3+1).

checksat[unsat] ldll(E1,F1,x1,E3,F3,x3) * ldll(E2,F2,x2,E4,F4,x4) * ldll(E3,F3,x3,E4,F4,x4) * ldll(E4,F4,y4,E3,F3,y3) * ldll(E3,F3,x3,E5,F5,x5) * ldll(E5,F5,y5,E3,F3,y3) * ldll(E4,F4,x5,E6,F6,x6) & x3 > x5 & E1 != E3.


                                                                    /*

!!! tree:
nodes:
id: 0
data: qvars: []
heap == hpred = ldll(E,P,len1,F,L,len2)_0(+1)^0
hptos = 
qf_eql_f = 
status: true
eql_f = 
status: true

arith == arith_pure = true
inv_preds = exists idx_19: len1=(idx_19+len2) & len1>=len2


parent: -1
children: [1,2]
h:0
status = reduced

id: 1
data: qvars: []
heap == hpred = 
hptos = 
qf_eql_f = E=F&P=L & 
status: true
eql_f = E=F&P=L & 
status: true

arith == arith_pure = len1=len2
inv_preds = exists idx_19: len1=(idx_19+len2) & len1>=len2


parent: 0
children: []
h:1
status = sat

id: 2
data: qvars: [u_29,len3_30]
heap == hpred = ldll(u_29,E,len3_30,F,L,len2)_1(+1)^0
hptos = E::RefDll_t<u_29,P>
qf_eql_f = E!=null
status: true
eql_f = Ex [u_29,len3_30]. E!=null
status: true

arith == arith_pure = len1=(1+len3_30)
inv_preds = exists idx_31: exists idx_19: len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2


parent: 0
children: [3,4]
h:1
status = reduced

id: 3
data: qvars: [u_29,len3_30]
heap == hpred = 
hptos = E::RefDll_t<u_29,P>
qf_eql_f = E=L & E!=null
status: true
eql_f = Ex [u_29,len3_30]. u_29=F&E=L & E!=null
status: true

arith == arith_pure = len1=(1+len3_30) & len3_30=len2
inv_preds = exists idx_31: exists idx_19: len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2


parent: 2
children: []
h:2
status = sat

id: 4
data: qvars: [u_29,len3_30,u_32,len3_33]
heap == hpred = ldll(u_32,u_29,len3_33,F,L,len2)_2(+1)^0
hptos = E::RefDll_t<u_29,P>*u_29::RefDll_t<u_32,E>
qf_eql_f = E!=null
status: true
eql_f = Ex [u_29,len3_30,u_32,len3_33]. E!=u_29 & E!=null&u_29!=null
status: true

arith == arith_pure = len1=(1+len3_30) & len3_30=(1+len3_33)
inv_preds = exists idx_34: exists idx_19: exists idx_31: len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len3_33=(idx_34+len2) & len3_33>=len2


parent: 2
children: [5,6]
h:2
status = reduced

id: 5
data: qvars: [u_29,len3_30,u_32,len3_33]
heap == hpred = 
hptos = E::RefDll_t<u_29,P>*u_29::RefDll_t<u_32,E>
qf_eql_f = E!=null
status: true
eql_f = Ex [u_29,len3_30,u_32,len3_33]. u_32=F&u_29=L & E!=u_29 & E!=null&u_29!=null
status: true

arith == arith_pure = len1=(1+len3_30) & len3_30=(1+len3_33) & len3_33=len2
inv_preds = exists idx_34: exists idx_19: exists idx_31: len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len3_33=(idx_34+len2) & len3_33>=len2


parent: 4
children: []
h:3
status = sat

id: 6
data: qvars: [u_29,len3_30,u_32,len3_33,u_35,len3_36]
heap == hpred = ldll(u_35,u_32,len3_36,F,L,len2)_3(+1)^0
hptos = E::RefDll_t<u_29,P>*u_29::RefDll_t<u_32,E>*u_32::RefDll_t<u_35,u_29>
qf_eql_f = E!=null
status: true
eql_f = Ex [u_29,len3_30,u_32,len3_33,u_35,len3_36]. E!=u_29&E!=u_32&u_29!=u_32 & E!=null&u_29!=null&u_32!=null
status: true

arith == arith_pure = len1=(1+len3_30) & len3_30=(1+len3_33) & len3_33=(1+len3_36)
inv_preds = exists idx_37: exists idx_31: exists idx_19: exists idx_34: len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len3_33=(idx_34+len2) & len3_33>=len2 & len3_36=(idx_37+len2) & len3_36>=len2


parent: 4
children: []
h:3
status = cycle


edges:
(0,[(ldll(E,P,len1,F,L,len2)_0(+1)^0,(exists : emp & E=F & P=L & len1=len2))],1)
(0,[(ldll(E,P,len1,F,L,len2)_0(+1)^0,(exists u_29,len3_30: E::RefDll_t<u_29,P> * ldll(u_29,E,len3_30,F,L,len2)_0(+1)^0 & len1=(1+len3_30)))],2)
(2,[(ldll(u_29,E,len3_30,F,L,len2)_1(+1)^0,(exists u_29,len3_30: emp & u_29=F & E=L & len3_30=len2))],3)
(2,[(ldll(u_29,E,len3_30,F,L,len2)_1(+1)^0,(exists u_29,len3_30,u_32,len3_33: u_29::RefDll_t<u_32,E> * ldll(u_32,u_29,len3_33,F,L,len2)_0(+1)^0 & len3_30=(1+len3_33)))],4)
(4,[(ldll(u_32,u_29,len3_33,F,L,len2)_2(+1)^0,(exists u_29,len3_30,u_32,len3_33: emp & u_32=F & u_29=L & len3_33=len2))],5)
(4,[(ldll(u_32,u_29,len3_33,F,L,len2)_2(+1)^0,(exists u_29,len3_30,u_32,len3_33,u_35,len3_36: u_32::RefDll_t<u_35,u_29> * ldll(u_35,u_32,len3_36,F,L,len2)_0(+1)^0 & len3_33=(1+len3_36)))],6)

back-links:(6,[(u_32,u_35),(u_29,u_32),(len3_33,len3_36),(F,F),(L,L),(len2,len2)],4)

*******************
* core program *
*******************
data Object {

}.


data __Exc {

}.


data RefDll_t {
  RefDll_t next@;;
  RefDll_t prev@;
}.


pred ldll< E,P,len1,F,L,len2> == emp & E=F & P=L & len1=len2 
  or (exists u_7,len3_8: E::RefDll_t<u_7,P> * ldll(u_7,E,len3_8,F,L,len2)_0(+1)^0 & len1=(1+len3_8))
 inv exists idx_19: len1=(idx_19+len2) & len1>=len2.
 precise_vars: Some(([],[(E,F)],[P,len1,L,len2])).
 bw vars: [].
 pred_unfolded_formula [].
 bases [emp & exists idx_19: E=F & P=L & len1=(idx_19+len2) & len1>=len2 & len1=len2,
(exists len3_30: E::RefDll_t<F,P> & exists idx_31: exists idx_19: E=L & E!=null & len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len1=(1+len3_30) & len3_30=len2),
(exists len3_30,len3_33: E::RefDll_t<L,P> * L::RefDll_t<F,E> & exists idx_34: exists idx_19: exists idx_31: E!=L & E!=null & L!=null & len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len3_33=(idx_34+len2) & len3_33>=len2 & len1=(1+len3_30) & len3_30=(1+len3_33))].
 buds [(exists u_29,len3_30,u_32,len3_33,u_35,len3_36: E::RefDll_t<u_29,P> * u_29::RefDll_t<u_32,E> * u_32::RefDll_t<u_35,u_29> & exists idx_37: exists idx_31: exists idx_19: exists idx_34: E!=u_29 & E!=u_32 & u_29!=u_32 & E!=null & u_29!=null & u_32!=null & len1=(idx_19+len2) & len1>=len2 & len3_30=(idx_31+len2) & len3_30>=len2 & len3_33=(idx_34+len2) & len3_33>=len2 & len3_36=(idx_37+len2) & len3_36>=len2 & len1=(1+len3_30) & len3_30=(1+len3_33) & len3_33=(1+len3_36))].
[selfrec; sat deci:true; ent deci:false; pure:false]



checksat ldll(E1,F1,x1,E3,F3,x3)_0(+1)^-1 * ldll(E2,F2,x2,E4,F4,x4)_0(+1)^-1 * ldll(E3,F3,x3,E4,F4,x4)_0(+1)^-1 * ldll(E4,F4,y4,E3,F3,y3)_0(+1)^-1 * ldll(E3,F3,x3,E5,F5,x5)_0(+1)^-1 * ldll(E5,F5,y5,E3,F3,y3)_0(+1)^-1 * ldll(E4,F4,x5,E6,F6,x6)_0(+1)^-1 & x5<x3 & E1!=E3.

*******************
* end core *
*******************
checksat ldll(E1,F1,x1,E3,F3,x3)_0(+1)^-1 * ldll(E2,F2,x2,E4,F4,x4)_0(+1)^-1 * ldll(E3,F3,x3,E4,F4,x4)_0(+1)^-1 * ldll(E4,F4,y4,E3,F3,y3)_0(+1)^-1 * ldll(E3,F3,x3,E5,F5,x5)_0(+1)^-1 * ldll(E5,F5,y5,E3,F3,y3)_0(+1)^-1 * ldll(E4,F4,x5,E6,F6,x6)_0(+1)^-1 & x5<x3 & E1!=E3.

unsat

*/
