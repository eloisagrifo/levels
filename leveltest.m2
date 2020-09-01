-- Installing the Package
uninstallPackage "Levels"
restart
loadPackage "Complexes"
installPackage "Levels"
check "Levels"

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

-- Tests for ghost with respect to a perfect complex
R = QQ[x,y]
G = freeResolution(R^1/ideal(x))
X = freeResolution(R^1/ideal(x,y^2))

ghost(G,X)
level(G,X)

H = Hom(G,X)
f = map(X,complex R^0,0)

i = min H
	Q = cover ker H.dd_i
	h = inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q)
	j = 0
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		m = map(X,G[-i],(map(X[i],G,homomorphism g,Degree => 0)[-i]))
		f = f | m
i = i+1
	Q = cover ker H.dd_i
	h = inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q)
	j = 0
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)
	j = 1
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)
	j = 2
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)
i = i+1
	Q = cover ker H.dd_i
	h = inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q)
	j = 0
		g = map(H,(complex R^1)[-i],k -> if k==-i then map(H_i,R^1,h*(id_Q)_{j}))
		f = append(f,homomorphism g)
	j = 1
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)
	j = 2
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)




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



--Testing level wrt G
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
R = QQ[x,y]
G = freeResolution(R^1/ideal(x))
X = freeResolution(R^1/ideal(x,y^2))
time level(X,complex(R^1), MaxLevelAttempts => 2) --0.2secs
time level(X,complex(R^1), MaxLevelAttempts => 3) --5 secs
time level(X,complex(R^1), MaxLevelAttempts => 4) -- more than 125 secs 

X = freeResolution(R^1/ideal(x,y^2))
G = complex(R^1)
rX = resolution X;
rG = resolution G;	
n = 0;
f = id_(rX);
g = f;
--while:
(not isNullHomotopic g)
f = ghost(rG,f.target);
f = (minimize f.target).cache.minimizingMap * f
g = f*g
n = n+1;





time level(X,G, MaxLevelAttempts => 5) --
ghost(X,G)

time level(X,G, MaxLevelAttempts => 3) -- takes 20 secs already
time level(X,G, MaxLevelAttempts => 5) --
ghost(X,G)


--testing the function carefully:
rX = resolution X
rG = resolution G
n = 0
f = id_(rX)
g = f
--the actual contents of the while to run separately
not isNullHomotopic g
f = ghost(rG,f.target);
f = (minimize f.target).cache.minimizingMap * f;
g = f*g;
n = n+1;

     
time	while ((not isNullHomotopic g) and (n < 10)) do (
		f = ghost(rG,f.target);
		f = (minimize f.target).cache.minimizingMap * f;
		g = f*g;
		n = n+1;
	);
	n
