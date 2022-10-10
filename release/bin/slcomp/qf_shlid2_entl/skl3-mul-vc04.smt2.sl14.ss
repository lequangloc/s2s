
ddata RefSL3_t {
    RefSL3_t n1;
    RefSL3_t n2;
    RefSL3_t n3;
}.

pred skl1<hd,ex> == 
    (emp & hd=ex)
     or (exists tl: hd::RefSL3_t<n1=tl,n2=null,n3=null> * skl1(tl,ex) & hd!=ex).

pred skl2<hd,ex> == 
    (emp & hd=ex)
     or (exists tl,Z1: hd::RefSL3_t<n1=Z1,n2=tl,n3=null> * skl1(Z1,tl) * skl2(tl,ex) & hd!=ex).

pred skl3<hd,ex> == 
    (emp & hd=ex)
     or (exists tl,Z1,Z2: hd::RefSL3_t<n1=Z1,n2=Z2,n3=tl> * skl1(Z1,Z2) * skl2(Z2,tl) * skl3(tl,ex) & hd!=ex).

pred skl11<hd,ex> == 
    (emp & hd=ex)
     or (exists tl: hd::RefSL3_t<n1=tl,n2=null,n3=null> * skl11(tl,ex) & hd!=ex).

pred skl21<hd,ex> == 
    (emp & hd=ex)
     or (exists tl,Z1: hd::RefSL3_t<n1=Z1,n2=tl,n3=null> * skl11(Z1,tl) * skl21(tl,ex) & hd!=ex).

pred skl31<hd,ex> == 
    (emp & hd=ex)
     or (exists tl,Z1,Z2: hd::RefSL3_t<n1=Z1,n2=Z2,n3=tl> * skl11(Z1,Z2) * skl21(Z2,tl) * skl31(tl,ex) & hd!=ex).


checkent skl31(x4,x5) * skl3(x5,x6) * x2::RefSL3_t<n1=x2_0_1,n2=x2_1,n3=x3> * skl1(x2_0_1,x2_1) * skl2(x2_1,x2_2) * x2_2::RefSL3_t<n1=x2_2_1,n2=x2_3,n3=null> * skl1(x2_2_1,x2_2_2) * x2_2_2::RefSL3_t<n1=x2_2_3,n2=null,n3=null> * x2_2_3::RefSL3_t<n1=x2_2_4,n2=null,n3=null> * skl1(x2_2_4,x2_3) * skl21(x2_3,x3) * skl3(x3,null)
    |- skl31(x2,null) * skl3(x4,x6).