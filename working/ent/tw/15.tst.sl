
ddata RefGTyp {
  RefGTyp f0;
  RefGTyp f1;
}.

pred BinPath<x:RefGTyp,y:RefGTyp> ==
 emp & x = y
or (exists xp,yp: x::RefGTyp<f0 = xp,f1 = yp> * BinPath(xp,y) & null != x)
or (exists xp,yp: x::RefGTyp<f0 = xp,f1 = yp> * BinPath(yp,y) & null != x).

checkent[valid] BinPath(x,z) * BinPath(z,y)
         |- BinPath(x,y).

