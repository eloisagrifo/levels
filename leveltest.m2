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
G = freeResolution(R^1/ideal(x,y))
X = freeResolution(R^1/ideal(x^5,y^2))

ghost(G,X)

H = Hom(G,X)
f = {}

	for i from min H to max H do (
		Q := cover ker H.dd_i;
		-- induced module map Q -> H_i
		h := inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q);
		for j from 0 to rank Q-1 do (
			-- complex map R^1[-i] -> H picking out the jth generator in degree i
			m := (id_Q)_{j}*h;
			g := map(H,(complex R^1)[-i],k -> if k==-i then (id_Q)_{j}*h);
			append(f,homomorphism g);
		)
	)

i = min H
	Q = cover ker H.dd_i
	h = inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q)
	j = 0
		g = map(H,(complex R^1)[-i],k -> if k==-i then h*(id_Q)_{j})
		f = append(f,homomorphism g)
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
