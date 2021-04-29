--not a problem
restart
needsPackage "Complexes"
needsPackage "ThickSubcategories";
needsPackage "CompleteIntersectionResolutions";
R = QQ[x,y,z]/ideal"x2,xy,yz,z2"
Y = complex koszul matrix{{x,y,z}}
time supportVariety(R^1)
time supportVariety(Y, FiniteLength => true)





--problem example
restart
needsPackage "Complexes"
needsPackage "ThickSubcategories";
needsPackage "CompleteIntersectionResolutions";
R = QQ[x,y]/ideal"x2,y2"
Y = complex koszul matrix{{y}}
time supportVariety(R^1)
time supportVariety(Y)
time supportVariety(Y,FiniteLength => true)


--problem example
restart
needsPackage "Complexes"
needsPackage "ThickSubcategories";
needsPackage "CompleteIntersectionResolutions";
R = QQ[x,y,z]/ideal"x2,xy,z2"
Y = complex koszul matrix{{z}}
time supportVariety(R^1)
time supportVariety(Y,FiniteLength => true)




--problem example
restart
needsPackage "Complexes"
needsPackage "ThickSubcategories";
needsPackage "CompleteIntersectionResolutions";

R = QQ[x,y,z,w]/ideal"x2,xy,yz,zw,w2"
X = complex koszul matrix{{x,y,z,w}}
time supportVariety(X)
time supportVariety(X,FiniteLength => true)

time supportVariety(R^1)






M = Y
N = complex(R^1 / ideal vars R)
    B = ring M;
    if not(B === ring(N)) then error "expected complexes over the same ring";
    if not isCommutative B
    then error "'Ext' not implemented yet for noncommutative rings";
    if not isHomogeneous B
    then error "'Ext' received modules over an inhomogeneous ring";
    if ((not isHomogeneous M) or (not isHomogeneous N))
    then error "received an inhomogeneous complex";
    
    p = presentation B
    A = ring p
    I = trim ideal p
    n = numgens A
    c = numgens I
    f = apply(c, i -> I_i)
    
    M' = restrict(M,A) -- homogeneous
    assert isHomogeneous M'; -- is this necessary, that is is there a way that the construction could give a non-homogeneous module?
    
    -- Construct ring of cohomological operators (over field)
    K = coefficientRing A
    X = getSymbol "X"
    S = K(monoid[X_1 .. X_c, toSequence gens A,
           Degrees => { apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
                        apply(0 .. n-1, j -> prepend( 0,   degree A_j))},
           Heft => {-2,1} ])
    -- Natural inclusion A -> S
    toS = map(S,A,apply(toList(c .. c+n-1), i -> S_i),DegreeMap => prepend_0)
    
    if (M == 0 or N == 0) then return S^0;
    
    C = chainComplex resolution(M')
    -- keys: {J,d} where J a list of integers of length c and d the degree of the source in C
    homotopies = makeHomotopies(matrix{f},C)
    
    -- Construct Cstar = (S \otimes_A C)^\natural
    degreesC = sort select(keys C, i -> class i === ZZ)
--     degreesC := toList(min(C)..max(C));
    Cstar = S^(apply(degreesC,i -> toSequence apply(degrees C_i, d -> prepend(i,d))))
    
    -- Construct the (almost) differential Delta: Cstar -> Cstar[-1] that combines the homotopies and multiplication by X_i
    -- We omit the sign (-1)^(n+1) which would ordinarily be used, which does not affect the homology.
    
    -- Return X^n = X_0^{n_0} *...* X_(c-1)^{n_{c-1}} for a list of integers n
    prodX = o -> product toList(apply(pairs o, i -> S_(i_0)^(i_1)))
    
    -- Create a matrix for each entry of homotopies
    r = rank Cstar
    ranksC = apply(degreesC, o -> rank(C_o))
    
    matrixfromblocks = (M) -> fold((a,b) -> a || b,apply(M, w -> fold((a,b) -> a | b, w)))
    makematrix = (L,M) -> (
        -- L a list {gamma,d} where gamma a list of integers of length c and d a degree of C
        -- M a matrix
        
        -- Problem if there are undefined degrees between minC and maxC
--         blockmatrix = table( #degreesC,
--                              #degreesC, 
--                              (p,q) -> if (p == L_1 + 2*(sum L_0) - 1 - min C) and (q == L_1 - min C) then M else map(A^(ranksC#p),A^(ranksC#q),0));
--         matrixfromblocks blockmatrix
        
        -- Find position to place M in
        topleftrow := sum take(ranksC, L_1 + 2*(sum L_0) - 1 - min C);
        topleftcolumn := sum take(ranksC, L_1 - min C);
        matrix table(r,r, (p,q) -> (
            if (
                (p >= topleftrow) and (p < (topleftrow + numRows M)) and 
                (q >= topleftcolumn) and (q < (topleftcolumn + numColumns M))
            ) then 
                M_(p-topleftrow,q-topleftcolumn) else 0
            )
        )
    );
    
    DeltaCmatrix = sum(apply(select(keys homotopies, 
		i -> homotopies#i != 0), i -> prodX(i_0)*toS(makematrix(i,homotopies#i))))
    DeltaC = map( Cstar,
                  Cstar, 
                  transpose DeltaCmatrix,
                  Degree => { -1, degreeLength A:0 })

    -- Rewrite N as a graded S-module D with a degree -1 map
    degreesN = toList((min N) .. (max N))
    Ndelta = apply(degreesN, i -> N.dd_i)
    Nmods = apply(degreesN, i -> tensor(S,toS,restrict(N_i,A)))
    Nmatrix = apply(Ndelta, f -> tensor(S,toS,restrict(f,A)))
    Nsize = apply(Nmods,numgens)
    Ntable = table(#Nmatrix,#Nmatrix, (p,q) -> if (p == (q-1)) then Nmatrix_(p+1) else map(S^(Nsize_p),S^(Nsize_q),0))
    
    DeltaNmatrix = matrixfromblocks Ntable
    Ngraded = fold((a,b) -> a ++ b,Nmods)
    DeltaN = map(Ngraded,Ngraded,DeltaNmatrix)
    
    SignIdCstar = diagonalMatrix flatten toList apply(pairs(ranksC), w -> if even(w_0) then apply(toList(1 .. w_1), o -> -1) else apply(toList(1 .. w_1), o -> 1))

    SignIdCstar = promote(SignIdCstar, S);
        
    DeltaBar = SignIdCstar ** DeltaN + DeltaC ** id_Ngraded;    

    H = prune homology(DeltaBar, DeltaBar);
    
    ann H

    C.dd
    
    SignIdCstar
    
    
    H

    ((ker SignIdCstar) / (image SignIdCstar)) == 0

    ((SignIdCstar)^2)_(7,8) 
    
    map(S^(64),S^(64))
    
     ((SignIdCstar)^2) == id_(S^(64))

    DeltaBar^2
    

    
    nonzerokeys = select(keys homotopies, o -> homotopies#o != 0)
    nonzeroes = apply(select(keys homotopies, o -> homotopies#o != 0), i -> homotopies#i)
    
    #nonzeroes
    
    i = 0
    i = i+1	
    nonzerokeys_i    
    nonzeroes_i
	
    nonzeroes_0 * nonzeroes_6
    nonzeroes_1 * nonzeroes_2
    
    nonzeroes_6
