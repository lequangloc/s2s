
data RefGTyp {
  RefGTyp f0;
  RefGTyp f1;
}.

pred I001<a:RefGTyp> ==
(exists a00: a::RefGTyp<f0 = a00,f1 = null> * I003(a,a00) & null != a).

pred ls<a:RefGTyp> ==
 emp & null = a
or I001(a) & null != a.

pred I3724<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp> ==
(exists a00: g::RefGTyp<f0 = a00,f1 = null> * I21063(a,b,c,d,e,f,g,a00) & null != g).

pred I21092<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp,h:RefGTyp> ==
I3724(a,b,c,d,e,f,h).

pred I3725<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp> ==
 emp & null = a
or I3752(a,b,c,d,e,f,g) & null != a.

pred I21093<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp,h:RefGTyp> ==
I3725(a,b,c,d,e,f,h).

pred I21063<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp,h:RefGTyp> ==
 I21093(a,b,c,d,e,f,g,h) & null = h
or I21092(a,b,c,d,e,f,g,h) & null != h.

pred I10117<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp,h:RefGTyp> ==
I3725(h,b,c,d,e,f,g).

pred I3752<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp> ==
(exists a00: a::RefGTyp<f0 = a00,f1 = null> * I10117(a,b,c,d,e,f,g,a00) & null != a).

pred I3670<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp> ==
 I3725(a,b,c,d,e,f,g) & null = g
or I3724(a,b,c,d,e,f,g) & null != g.

pred I3572<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp> ==
(exists a00: f::RefGTyp<f0 = a00,f1 = null> * I3670(a,b,c,d,e,f,a00) & null != f).

pred I3573<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp> ==
 emp & a = f
or I3623(a,b,c,d,e,f) & a != f.

pred I3633<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp,g:RefGTyp> ==
I3573(g,b,c,d,e,f).

pred I3623<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp> ==
(exists a00: a::RefGTyp<f0 = a00,f1 = null> * I3633(a,b,c,d,e,f,a00) & null != a).

pred I3552<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp> ==
 I3573(a,b,c,d,e,f) & null = f
or I3572(a,b,c,d,e,f) & null != f.

pred I634<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp> ==
(exists a00: e::RefGTyp<f0 = a00,f1 = null> * I3552(a,b,c,d,e,a00) & null != e).

pred I635<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp> ==
 emp & b = e
or I664(a,b,c,d,e) & b != e.

pred I2011<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp,f:RefGTyp> ==
I635(a,f,c,d,e).

pred I664<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp> ==
(exists a00: b::RefGTyp<f0 = a00,f1 = null> * I2011(a,b,c,d,e,a00) & null != b).

pred I618<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp> ==
 I635(a,b,c,d,e) & null = e
or I634(a,b,c,d,e) & null != e.

pred I046<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp> ==
(exists a00: d::RefGTyp<f0 = a00,f1 = null> * I618(a,b,c,d,a00) & null != d).

pred I047<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp> ==
 emp & b = d
or I088(a,b,c,d) & b != d.

pred I337<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp,e:RefGTyp> ==
I047(a,e,c,d).

pred I088<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp> ==
(exists a00: b::RefGTyp<f0 = a00,f1 = null> * I337(a,b,c,d,a00) & null != b).

pred I034<a:RefGTyp,b:RefGTyp,c:RefGTyp,d:RefGTyp> ==
 I047(a,b,c,d) & null = d
or I046(a,b,c,d) & null != d.

pred I021<a:RefGTyp,b:RefGTyp,c:RefGTyp> ==
(exists a00: c::RefGTyp<f0 = a00,f1 = null> * I034(a,b,c,a00) & null != c).

pred I008<a:RefGTyp,b:RefGTyp> ==
emp.

pred I022<a:RefGTyp,b:RefGTyp,c:RefGTyp> ==
I008(b,c).

pred I013<a:RefGTyp,b:RefGTyp,c:RefGTyp> ==
 I022(a,b,c) & null = c
or I021(a,b,c) & null != c.

pred I007<a:RefGTyp,b:RefGTyp> ==
(exists a00: b::RefGTyp<f0 = a00,f1 = null> * I013(a,b,a00) & null != b).

pred I003<a:RefGTyp,b:RefGTyp> ==
 I008(a,b) & null = b
or I007(a,b) & null != b.


checksat[sat] ls(x0).

