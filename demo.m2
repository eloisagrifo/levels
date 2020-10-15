restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
Q = QQ[x,y]
I = ideal"xy,x2"
nonProxySmall(I)


restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
Q = QQ[x,y,z]
I = ideal(x^2-y^2, x^2-z^2, x*y, y*z, x*z)
time nonProxySmall(I)

restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
T = QQ[s,t]
Q = QQ[a,b,c,d]
I = ker map(T,Q,{s^3, s^2*t, s*t^2, t^3})
J = nonProxySmall I


restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
T = QQ[s,t,u]
R = QQ[x_1 .. x_(10)]
I = ker map(T,R,{s^3, s^2*t, s^2*u, s*t^2, s*t*u, s*u^2, t^3, t^2*u, t*u^2, u^3});
J = nonProxySmall I -- 23secs


--non-equipresented
restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
Q = QQ[x,y,z]
I = ideal"x2+y2+z2,xyz,x3"
M = Q^1/ideal"x2+y2+z2,y,x3"
R = Q/I
M = M ** R;
isBuilt(R^1,M)
supportVariety(R^1)
