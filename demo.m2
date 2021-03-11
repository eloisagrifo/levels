--Over a ci
--we can check if two modules or complexes build each other
restart
path = append(path, "~/Documents/GitHub/levels");
loadPackage "ThickSubcategories";
Q = QQ[x,y]
I = ideal"x2,y2"
R = Q/I
k = R^1/ideal"x,y"
M = R^1/ideal(x)
N = R^1/ideal(y)
isBuilt(M,N)--N doesn't build M
isBuilt(N,M)--M doesn't build N
isBuilt(k,M)--M doesn't build k
isBuilt(k,N)--N doesn't build k
--but M and N are both finite length
--so they are both built by k
isBuilt(M,k)
isBuilt(N,k)

--Over a non-ci
--we can still give negative answers
--and say M doesn't build N
--but we can't give positive answers without computing levels
restart
path = append(path, "~/Documents/GitHub/levels");
needsPackage "ThickSubcategories";
Q = QQ[a,b,c]
I = ideal"ab,bc"
R = Q / I
m = ideal vars R
k = R^1/ m
M = R^1 / (m^2)
time isBuilt(M,k)
time isBuilt(k,M)

--another non-ci example
restart
path = append(path, "~/Documents/GitHub/levels");
needsPackage "ThickSubcategories";
needsPackage "Complexes"
R = QQ[x,y]/ideal"x2,xy"
K = complex koszul(matrix{{x,y}})
M = complex(R^1/ideal"x")
N = complex(R^1/ideal"y")
time isBuilt(K,M)
time isBuilt(K,N)
--Both these modules M and N are NOT proxy small!
--A module is virtually small iff it builds the koszul complex


--fun examples of levels
restart
path = append(path, "~/Documents/GitHub/levels");
needsPackage "ThickSubcategories";
needsPackage "Complexes"
R = QQ[x]
M = R^1/ideal"x3"
N = R^1/ideal"x7"
L = R^1/ideal"x17"
K = R^1/ideal"x23"
time level(M,N)
time level(M,L)
time level(M,K)




restart
path = append(path, "~/Documents/GitHub/levels");
needsPackage "ThickSubcategories";
needsPackage "Complexes"
R = QQ[x,y,z]
M = complex koszul(matrix{{x*y,y*z,x*z}}) 
N = complex koszul(matrix{{x}})
time level(M,N)--number of steps to build N from M
time isBuilt(M,N)--but cannot build M from N
