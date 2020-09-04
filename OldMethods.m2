-- The ghost method works, but is inefficient
ghost(Complex,Complex) := (G,X) -> (
	R := ring G;
	
	H := Hom(G,X);
	
	-- This going to be the approximation
	f := map(X,complex R^0,0);
	-- Find generators of H: maps f_i: G[n_i] -> X
	for i from min H to max H do (
		Q := cover ker H.dd_i;
		-- induced module map Q -> H_i
		h := inducedMap(H_i,ker H.dd_i)*map(ker H.dd_i,Q,id_Q);
		for j from 0 to rank Q-1 do (
			-- complex map R^1[-i] -> H picking out the jth generator in degree i
			g := map(H,(complex R^1)[-i],k -> if k==i then map(H_i,R^1,h*(id_Q)_{j}));
			f = f | map(X,G[-i],(map(X[i],G,homomorphism g,Degree => 0)[-i]));
		);
	);
	canonicalMap(cone(f),X)
)

-- The computations of level/ghost wrt to R^1 are not more efficient than using the more general method
ghost(Complex) := (F) -> (
	R := ring F;
	
	-- Construct the R-approximation of F
	Q := complex R^0;
	for i from min F to max F do Q = Q ++ complex(cover ker F.dd_i)[-i];
	
	-- Construct map Q -> F
	fun := i -> if (i >= min F or i <= max F) then inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q_i,id_(Q_i)) else map(R^0,F_i);
	
	-- Take the cone
	G := cone(map(F,Q,fun));
	
	-- Return the map F -> G
	canonicalMap(G,F)
)
level(Complex) := ZZ => opts -> (G) -> (
	-- We need G to be a complex of free/projective modules, so that any map from G is zero iff it is null homotopic
	G = resolution G;	
	n := 0;
	f := id_G;
	g := f;
	-- As long as the composition of the ghost maps g is non-zero, continue
	while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
		f = ghost f.target;
		f = (minimize f.target).cache.minimizingMap * f;
		g = f*g;
		n = n+1;
	);
	n
)
