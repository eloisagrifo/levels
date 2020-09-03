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
time level(X)
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
level(X)


--more testing wrt G
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
R = QQ[x]
rX = freeResolution(R^1/ideal(x))
rG = complex(R^1)
n = 0;
f = id_(rX);
g = f;
--while
(not isNullHomotopic g)
f = ghost(rG,f.target);
f = (minimize f.target).cache.minimizingMap * f
g = f*g
n = n+1;

	L := {f};
for i from min H to max H do (
	    	K := ker H.dd_i;
		Q := cover K;
		-- induced module map Q -> H_i
		h := inducedMap(H_i,K)*map(K,Q,id_Q);
		for j from 0 to rank Q-1 do (
			-- complex map R^1[-i] -> H picking out the jth generator in degree i
			g := map(H,(complex R^1)[-i],k -> if k==i then map(H_i,R^1,h*(id_Q)_{j}));
			L = append(L,map(X,G[-i],(map(X[i],G,homomorphism g,Degree => 0)[-i])));
		);
	);
    	f = fold((a,b) -> a | b,L);
	canonicalMap(cone(f),X)



--May be the problem: shifting maps
g := map(H,(complex R^1)[-i],k -> if k==-i then map(H_i,R^1,h*(id_Q)_{j}));
map(X,G[-i],(map(X[i],G,homomorphism g,Degree => 0)[-i])));




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





--more testing wrt G
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
R = QQ[x_1 .. x_6]
M = complex(R^1/minors(2,matrix{{x_1, x_2, x_3},{x_4, x_5, x_6}}))
N = complex(R^1/ideal(x_1,x_2,x_3))
time level(N,M)




--more testing wrt G
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
R = QQ[x]
--answer is 3
N = complex(R^1/ideal(x^3))
M = complex(R^1/ideal(x^7))
time level(N,M)
	-- We need X to be a complex of free/projective modules, so that any map from X is zero iff it is null homotopic
	rX = resolution k;
	rG  = resolution k;	
	n  = 0;
	f := id_(rX);
	g := f;
	-- As long as the composition of the ghost maps g is non-zero, continue
	while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
		f = ghost(rG,f.target);
		f = (minimize f.target).cache.minimizingMap * f;
		g = f*g;
		n = n+1;
	);
	n
)


--more testing wrt G
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Complexes";
installPackage "Levels"
check "Levels"
R = QQ[x,y]
M = complex(R^1/ideal(x^2,y^2))
N = complex(R^1/ideal(x,y))
time level(M,N)




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
