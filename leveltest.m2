-- Installing the Package
uninstallPackage "Levels"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "Levels"
check "Levels"
loadPackage "Complexes"

---------------------------------------------------------------
-- Tests for level wrt R^1
R = QQ[x,y,z]

F = complex R^0
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 0

F = complex R^2
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 1

R = QQ[x,y,z]/ideal(x*y*z)
G = complex R^2
F = G ++ G[1] ++ G[-1]
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 1

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)[-3]
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I^2)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x]
I = ideal vars R
F = complex(R^1/I)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 2

---------------------------------------------------------------
-- Tests for ghost with respect to a perfect complex
R = QQ[x,y]
G = freeResolution(R^1/ideal(x), LengthLimit => 10)
X = freeResolution(R^1/ideal(x,y^2))
time level(G,X)
time level(G,X,Strategy => "coghost")
-- Correct answer: 2

R = QQ[x_1 .. x_6]
M = complex(R^1/minors(2,matrix{{x_1, x_2, x_3},{x_4, x_5, x_6}}))
N = complex(R^1/ideal(x_1,x_2,x_3))
time level(N,M)

R = QQ[x]
N = complex(R^1/ideal(x^3))
M = complex(R^1/ideal(x^7))
time level(N,M)

R = QQ[x,y]
M = complex(R^1/ideal(x^2,y^2))
N = complex(R^1/ideal(x,y))
time level(M,N)


<<<<<<< HEAD
----local stuff
path=append(path,"~/Documents/EJJ/levels");
installPackage "Levels"


f=ghost(F)
isNullHomotopic f
=======

uninstallPackage "Complexes"
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
installPackage "Complexes"
loadPackage "Complexes"
check "Levels"
R = QQ[x]
ghost(R^1)
freeResolution(R^1)
>>>>>>> 7ba705011522f72d3afc94c4618390bed1a99c43



--testing isPerfect
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
check "Levels"
R = QQ[x,y]
M = complex(R^1/ideal(x^2,y^2))
isPerfect (complex(M))
N = complex(R^1/ideal(x,y))
time level(M,N)

F = N
isPerfect=method();
isPerfect(Complex) := (F) -> (
    R := ring F;
    m := ideal(vars R);
    k := complex(R^1/m);
    d := dim(R)+max(F)+1;
    G := resolution(F);
    T := tensor(G,k);
    HH_d(T)==0   
)

-- Error for level
-- Level
R = ZZ[x,a]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x*a,a^2}})
f2 = map(source f1,,matrix{{x*a},{-x^2}})
F = complex{f1,f2}
isWellDefined F
level(F,MaxLevelAttempts => 4)
-- Level should be <= 3

R = ZZ[x]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x,1}})
f2 = map(source f1,,matrix{{x},{-x^2}})
F = complex{f1,f2}
isWellDefined F
level(F,MaxLevelAttempts => 4)
-- This makes no sense, since F is not exact (or equivalently id_F is not nullhomotopic)
isExact F
isNullHomotopic id_F

-- Problem is that resolution does not work as it should:
R = ZZ[x]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x,1}})
f2 = map(source f1,,matrix{{x},{-x^2}})
F = complex{f1,f2}
isQuasiIsomorphism(resolutionMap F)
-- It probably does not work since F is not homogeneous


?level

ann M


--Testing support varieties
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
R = QQ[x]/ideal(x^2)
M = R^1/ideal(x)
time isBuilt(M,R^1)


R = QQ[x,y,z]/ideal"x2,y2,z2"
k = R^1/ideal(x,y,z)
M = R^1/ideal"x,y"
time isBuilt(k,R^1)
time isBuilt(R^1,k)
time isBuilt(M,R^1)
time isBuilt(R^1,M)

supportVariety(M)
N = R^1/ideal(x,y^2,z^2)
time isBuilt(N,R^1)
time isBuilt(R^1,N)

E1 = extKoszul(M)
E2 = extKoszul(R^1)
S = ring E1
T = ring E2
M


--testing isBuilt
R = QQ[x,y,z]/ideal"x2,yz"
M = R^1/ideal(x,y)
time isBuilt(M,R^1)
time isBuilt(R^1,M)
time level(R^1,M) -- returns 5 but should be infinity!
time level(M,R^1, MaxLevelAttempts => 20)
supportVariety(M)
N = R^1/ideal(x,y^2,z^2)
time isBuilt(N,R^1)
time isBuilt(R^1,N)



--changing freeResolution options
uninstallPackage "Complexes"
restart
installPackage "Complexes"
viewHelp freeResolution

R = QQ[x,y,z]/ideal"x2,yz"
M = R^1/ideal(x,y)
freeResolution(M, LengthLimit => 10)


--testing nonProxySmall
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
Q = QQ[x,y,z]
I = ideal(x^2-y^2, x^2-z^2, x*y, y*z, x*z)
time nonProxySmall I

-- Compare different methods for level wrt R^1
uninstallPackage "Levels"
restart
loadPackage "Complexes"
installPackage "Levels"

R = QQ[x,y,z]
X = R^1/ideal(x^2,y^2,z^2)
f1 = map(R^1,R^2,matrix{{x,y^2}})
f2 = map(source f1,X,matrix{{x},{1}})
F = complex{f1,f2}

R = QQ[x]/ideal(x^2)
X = complex(R^4/ideal(x))
time level(X,MaxLevelAttempts => 5)
time level(R^1,X,MaxLevelAttempts => 5)
Y = complex(R^1) ++ X[2]
time level(Y,MaxLevelAttempts => 10)
time level(complex R^1,Y,MaxLevelAttempts => 10)

-- Some example
R = QQ[x,y]
needsPackage("Complexes");
F = complex(R^0)
G = freeResolution(R^1/ideal(x))
X = freeResolution(R^1/ideal(x,y^2))
level(G,X)  

-- Truncations of the resolution and how they affect the result of level
R = QQ[x]/ideal(x^2)
X = complex(R^1/ideal(x))
resolution(X,LengthLimit => 5)
resolution(X[3],LengthLimit => 5) == resolution(X[3]++X[-3],LengthLimit => 5)
-- Examples that explore this weakness
R = QQ[x,y]
X = complex(R^1/ideal(x,y))
level(X,X++X[-2],MaxLevelAttempts => 3)
-- This should be 1, but returns 3
level(X,X++X[-4],MaxLevelAttempts => 6)



uninstallPackage "Levels"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "Levels"
Q = QQ[x,y]
I = ideal"xy,x2"
nonProxySmall(I)
R = Q/I
nonProxySmall(R)
M1 = R^1/ideal"y"
M2 = R^1/ideal"x+y"
M3 = R^1/ideal"x"
isBuilt(R^1,M1)
isBuilt(R^1,M2)
isBuilt(R^1,M3)
isBuilt(R^1,R^1/ideal"x,y")
k = R^1/ideal(x,y)
isBuilt(k,R^1)
d = depth R + 3
time level(R^1,k,MaxLevelAttempts => d, LengthLimit => d)

-- Installing the Package
uninstallPackage "ThickSubcategories"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "ThickSubcategories"
check "ThickSubcategories"
needsPackage "Complexes"

-----------------------------------------------------------
-- Test if it makes sense to cut off the lower degree at the end of the while loop

R = QQ[x,y]
X = freeResolution coker vars R
time level X
-- 0.220509
-- 0.183668

R = QQ[x,y]/ideal(x^2)
X = freeResolution(R^1/ideal(y^2))
time level X
-- 0.133126
-- 0.127081

R = QQ[x,y,z]/ideal(x*y,y*z,z*x,x+y+z)
X = freeResolution(coker vars R,LengthLimit => 3)
time level X
-- 1.73377
-- 0.949323

R = QQ[x,y,z]/ideal(x*y,y*z,z*x,x+y+z)
X = freeResolution(coker vars R,LengthLimit => 4)
time level X
-- 21.9887
-- 6.78384


----------------------------------------------------------------------------
-- Test for restriction of scalars

uninstallPackage "ThickSubcategories"
restart
installPackage "ThickSubcategories"
needsPackage "Complexes"

R = QQ[x,y,z]/ideal(x^3,x*y)
M = R^1/ideal(y)
N = R^1/ideal(x,y)
f = inducedMap(N,M)

restrict f

p = presentation R
Q = ring p
I = trim ideal p
c = numgens I
f = apply(c,i->I_i)

pM = lift(presentation M,Q)
M' = cokernel(pM | p ** id_(target pM) )






