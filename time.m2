restart
path=append(path,"~/Documents/Github/levels");
path=append(path,"~/Dropbox/BEJ/m2");
load "supportVarieties.m2"
needsPackage "ThickSubcategories"
needsPackage "Complexes"
R=QQ[x,y,z,w]/ideal(x^2,x*y,y*z,z*w,w^2) 
time O1 = extKoszul(complex(R^1),complex(R^1))
time O2 = ExtE(R^1,R^1)



restart
path=append(path,"~/Documents/Github/levels");
path=append(path,"~/Dropbox/BEJ/m2");
load "supportVarieties.m2"
needsPackage "ThickSubcategories"
needsPackage "Complexes"
R=QQ[x,y,z,w]/ideal(x^2,x*y,y*z,z*w,w^2) 
time extKoszul(complex(R^1),complex(R^1))
time ExtE(R^1,R^1)
