-- Installing the Package
uninstallPackage "Levels"
restart
loadPackage "Complexes"
installPackage "Levels"
check "Levels"

---------------------------------------------------------------
-- Tests for level wrt R^1
R = QQ[x,y,z]

F = complex R^0
time level F
time level(R^1,F)
-- Correct answer: 0

F = complex R^2
time level F
time level(R^1,F)
-- Correct answer: 1

R = QQ[x,y,z]/ideal(x*y*z)
G = complex R^2
F = G ++ G[1] ++ G[-1]
time level F
time level(R^1,F)
-- Correct answer: 1

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)
time level F
time level(R^1,F)
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)[-3]
time level F
time level(R^1,F)
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I^2)
time level F
time level(R^1,F)
-- Correct answer: 4

R = QQ[x]
I = ideal vars R
F = complex(R^1/I)
time level F
time level(R^1,F)
-- Correct answer: 2

---------------------------------------------------------------
-- Tests for ghost with respect to a perfect complex
R = QQ[x,y]
G = freeResolution(R^1/ideal(x))
X = freeResolution(R^1/ideal(x,y^2))
time level(G,X)
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




--Testing support varieties
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
R = QQ[x]/ideal(x^2)
M = R^1/ideal(x)
time isBuilt(M,R^1)

R = QQ[x,y,z]/ideal"x2,yz"
M = R^1/ideal(x,y)
time isBuilt(M,R^1)
time isBuilt(R^1,M)
level(R^1,M)
supportVariety(M)
