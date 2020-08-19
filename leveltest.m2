uninstallPackage "Levels"
restart
loadPackage "Complexes"
path = append(path,"~/Dropbox/LevelsM2");
installPackage "Levels"

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

-- level does not work if the complex is not a complex of free modules
-- works now, since we take a resolution of G in level
R = QQ[x]
I = ideal vars R
F = complex(R^1/I)
assert(level F === 2)

-- Tests
R = QQ[x]
I = ideal vars R
G = complex(R^1/I)
n = 1
f = ghost G
g = f

-- F = f.target
-- Q = complex R^0;
-- for i from min F to max F do Q = Q ++ complex(cover ker F.dd_i)[-i];
-- fun = i -> if (i >= min F or i <= max F) then inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q_i,id_(Q_i)) else map(R^0,F_i);
-- H = cone(map(F,Q,fun))
-- canonicalMap(H,F)

f = ghost f.target
g = f*g
n = n+1
-- Problem: g is zero in D(R), not in K(R), that is first take a free resolution of the source, then the induced map is null-homotopic
-- Solution: Take the resolution at the beginning of level








