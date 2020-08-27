uninstallPackage "Levels"
restart
loadPackage "Complexes"
path = append(path,"~/Dropbox/LevelsM2");
installPackage "Levels"

-- Tests
R = QQ[x,y,z]

F = complex R^0
assert(level F == 0)

F = complex R^2
assert(level F == 1)

R = QQ[x,y,z]/ideal(x*y*z)
G = complex R^2
F = G ++ G[1] ++ G[-1]
assert(level F == 1)

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)
assert(level F == 4)

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)[-3]
assert(level F == 4)

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I^2)
assert(level F == 4)

R = QQ[x]
I = ideal vars R
F = complex(R^1/I)
assert(level F === 2)

----local stuff
path=append(path,"~/Documents/EJJ/levels");
installPackage "Levels"


f=ghost(F)
isNullHomotopic f
