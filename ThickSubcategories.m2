newPackage(
    "ThickSubcategories",
    Version => "1.0", 
    Date => "August 27, 2020",
    Authors => {
        {Name => "Eloisa Grifo", Email => "eloisa.grifo@ucr.edu", HomePage => "http://www-personal.umich.edu/~grifo/"},
        {Name => "Janina C. Letz", Email => "jletz@math.uni-bielefeld.de", HomePage => "http://www.math.uni-bielefeld.de/~jletz"},
        {Name => "Josh Pollitz", Email => "pollitz@math.utah.edu", HomePage => "http://www.math.utah.edu/~pollitz"}
    },
    Headline => "Computing levels of complexes",
    DebuggingMode => true
)

export {
    -- Options 
    "MaxLevelAttempts",
    "LengthLimitGenerator",
    "FiniteLength",
    "ResidueField",
    "RankVariety",
    "RankVarietyFast",
    "Koszul",
    -- Methods
    "ghost",
    "coghost",
    "level",
    "isPerfect",
    "supportVariety",
    "isBuilt",
    "nonProxySmall",
    "extKoszul",
    "higherHomotopies",
    "rightApproximation",
--    "findgs",
    "restrict",
    "exts",
    "supportMatrices"
}

needsPackage "CompleteIntersectionResolutions"
needsPackage "Complexes"
needsPackage "Depth"
needsPackage "MinimalPrimes"
needsPackage "FastMinors"

---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-- Construct a right G-approximation
---------------------------------------------------------------
rightApproximation = method( TypicalValue => ComplexMap );

rightApproximation(Complex,Complex) := ComplexMap => (G,X) -> (
    -- Input: G needs to be a complex of projective or free modules
    -- Check that G and X are complexes over the same ring
    R := ring G;
    if not(R === ring X) then error "expected complexes over the same ring";
    
    -- JL: This is overkill, we only need the degree 0 piece, as well as the maps (to and) from 0
    -- The Hom-sets in D(Mod(R)) are the homology of H
    H := Hom(G,X);
    
    -- Collect the generators of H_0(H), they are maps G -> X
    -- JL: There are two ways to compute them, via the homology or the kernel. Need to run more test to see which is more efficient.
    -- Using the kernel
    K := trim ker H.dd_0;
    Q := cover K;
    h := inducedMap(H_0,K)*map(K,Q,id_Q);
    
    -- Using the homology
    -- K := trim ker H.dd_0;
    -- L := trim HH_0 H;
    -- Q := cover L;
    -- h := inducedMap(H_0,K) * (map(L,Q,id_Q) // inducedMap(L,K));
    
    -- for each generator of Q pick the corresponding map G -> X
    generatorToMorphism := (j) -> homomorphism(map(H,(complex R^1),k -> if k==0 then map(H_0,R^1,h*Q_{j})));
    
    -- Combine all the maps G -> X
    return fold((a,b) -> a | b,map(X,G,0),apply(toList(0..(rank Q-1)),j -> generatorToMorphism(j)))
)

-- Creates a right R-approximation
rightApproximation(Complex,ZZ) := ComplexMap => (X,n) -> (
    R := ring X;
    
    Q := fold((a,b) -> a ++ b,complex R^0,apply(toList((min X)..n),i -> complex(cover ker X.dd_i)[-i]));
    
    -- Construct map Q -> X
    fun := i -> if (i >= min X or i <= n) then inducedMap(X_i,ker X.dd_i)*map(ker X.dd_i,Q_i,id_(Q_i)) else map(R^0,X_i);
    
    return map(X,Q,fun);
    
    -- something is wrong!!
    -- return map(X,complex(R^1,Base => n), k -> if k == 0 then inducedMap(X_n,ker X.dd_n) * coverMap ker X.dd_n)
)

---------------------------------------------------------------
-- Construct a left G-approximation
---------------------------------------------------------------
leftApproximation = method( TypicalValue => ComplexMap );

-- JL: Basically the same code as for rightApproximation, make an auxiliary method?
leftApproximation(Complex,Complex) := ComplexMap => (G,X) -> (
    -- Input: X needs to be a complex of projective or free modules
    -- Check that G and X are complexes over the same ring
    R := ring G;
    if not(R === ring X) then error "expected complexes over the same ring";
    
    -- JL: This is overkill, we only need the degree 0 piece, as well as the maps (to and) from 0
    -- The Hom-sets in D(Mod(R)) are the homology of H
    H := Hom(X,G);
    
    -- Collect the generators of H_0(H), they are maps X -> G
    -- JL: There are two ways to compute them, via the homology or the kernel. Need to run more test to see which is more efficient.
    -- Using the kernel
    K := trim ker H.dd_0;
    Q := cover K;
    h := inducedMap(H_0,K)*map(K,Q,id_Q);
    
    -- Using the homology
    -- K := trim ker H.dd_0;
    -- L := trim HH_0 H;
    -- Q := cover L;
    -- h := inducedMap(H_0,K) * (map(L,Q,id_Q) // inducedMap(L,K));
    
    -- for each generator of Q pick the corresponding map X -> G
    generatorToMorphism := (j) -> homomorphism(map(H,(complex R^1),k -> if k==0 then map(H_0,R^1,h*Q_{j})));
    
    -- Combine all the maps X -> G
    return fold((a,b) -> a || b,map(G,X,0),apply(toList(0..(rank Q-1)),j -> generatorToMorphism(j)))
)

---------------------------------------------------------------
-- Create the G-ghost map associated to the right G-approximation
---------------------------------------------------------------
ghost = method( TypicalValue => ComplexMap );

-- Creates a map f with source X such that Hom(G[-n],f) = 0 for every n in L
ghost(Complex,Complex,List) := ComplexMap => (G,X,L) -> (
    -- Input: G needs to be a complex of projective or free modules
    -- Input: L is a list of integers
    
    f := fold((a,b) -> a | b,apply(L,n -> rightApproximation(G[-n],X)));
    
    return canonicalMap(cone(f),X)
)

ghost(Complex,Complex) := ComplexMap => (G,X) -> (
    -- ghost(G,X,toList((min X - max G)..(max G + min G)))
    ghost(G,X,{0})
)

-- Creates an R[-n]-ghost map for every n in L
ghost(Complex,List) := ComplexMap => (X,L) -> (
    
    f := fold((a,b) -> a | b, apply(L,n -> rightApproximation(X,n)));
    
    return canonicalMap(cone(f),X)
)

-- Creates an R-ghost map with source X
ghost(Complex) := ComplexMap => (X) -> (
    -- ghost(X,toList((min X)..(max X)))
    ghost(X,{0})
)

---------------------------------------------------------------
-- Create the G-coghost map associated to the left G-approximation
---------------------------------------------------------------
coghost = method( TypicalValue => ComplexMap );

coghost(Complex,Complex,List) := ComplexMap => (G,X,L) -> (
    -- Input: X needs to be a complex of projective or free modules
    -- Input: L is a list of integers
    
    f := fold((a,b) -> a || b,apply(L,n -> leftApproximation(G[n],X)));
    
    return canonicalMap(X[-1],cone(f))[1]
)

coghost(Complex,Complex) := ComplexMap => (G,X) -> (
    -- Input: X needs to be a complex of projective or free modules
    return coghost(G,X,{0});
)

coghost(Complex,List) := ComplexMap => (X,L) -> (
    coghost(complex((ring X)^1),X,L)
)

coghost(Complex) := ComplexMap => (X) -> (
    return coghost(X,{0})
)

---------------------------------------------------------------
-- Compute the level of X with respect to G
---------------------------------------------------------------
level = method( TypicalValue => ZZ,
                Options => { MaxLevelAttempts => 10,
                             LengthLimit => 10,
                             LengthLimitGenerator => 5,
                             Strategy => "ghost" } );

level(Complex,Complex,List) := ZZ => opts -> (G,X,L) -> (
    -- Check that G and X are complexes over the same ring
    if not(ring G === ring X) then error "expected complexes over the same ring";
    
    if (X == 0) then return 0; -- needed because resolution does not work for the zero complex
    
    -- We need G to be a complex of free/projective modules to compute Ext
    rG := resolution(G, LengthLimit => opts.LengthLimitGenerator);
    -- We need X to be a complex of free/projective modules, so that any map from X is zero iff it is null homotopic
    rX := resolution(X, LengthLimit => opts.LengthLimit);
    n := 0;
    f := id_(rX);
    g := f;
    homogeneous := isHomogeneous X;
    if (opts.Strategy == "coghost") then ( -- Coghost maps
        -- As long as the composition of the ghost maps g is non-zero, continue
        while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
            rX = f.source;
            f = coghost(rG,rX,L);
            
            g = g*f;
            n = n+1;
        );
    ) else ( -- Ghost maps
        -- As long as the composition of the ghost maps g is non-zero, continue
        while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
            rX = f.target;
            f = ghost(rG,rX,L);
            
            -- minimize if possible
            if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
            
            g = f*g;
            n = n+1;
        );
    );
    n
)

-- Level with respect to R
level(Complex,List) := ZZ => opts -> (X,L) -> (
    if (X == 0) then return 0; -- needed because resolution does not work for the zero complex
    
    rX := resolution(X, LengthLimit => opts.LengthLimit);
    n := 0;
    f := id_(rX);
    g := f;
    i := min X;
    homogeneous := isHomogeneous X;
    -- The strategy decides whether ghost or coghost maps are used
    if (opts.Strategy == "coghost") then ( -- Coghost maps
        -- For coghost maps there is no `better' way for level wrt to R
        n = level((ring X)^1,rX,L, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => 0, Strategy => opts.Strategy);
    ) else ( -- Ghost maps
        -- As long as the composition of the ghost maps g is non-zero, continue
        while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
            rX = f.target;
            f = ghost(rX,L);
            -- minimize if possible
            if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
            
            -- The target always has zeros in degrees <= i+n, so those degrees do not play a role when testing if the map is null-homotopic
            g = f*g;
            n = n+1;
        );
    );
    n
)

level(Module,List) := ZZ => opts -> (M,L) -> (
    X := complex(M);
    level(X,L, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, Strategy => opts.Strategy)
)

level(Module,Module,List) := ZZ => opts -> (M,N,L) -> (
    level(complex(M),complex(N),L, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
)

level(Module,Complex,List) := ZZ => opts -> (M,X,L) -> (
    level(complex(M),X,L, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
)

level(Complex,Module,List) := ZZ => opts -> (G,N,L) -> (
    level(G,complex(N),L, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
)

---------------------------------------------------------------
-- Detects whether a complex is perfect
---------------------------------------------------------------
isPerfect = method( TypicalValue => Boolean );

isPerfect(Complex) := Boolean => (F) -> (
    -- Ring and its residue field for the complex F
    R := ring F;
    m := ideal(vars R);
    k := complex(R^1/m);
    
    -- Define the one homological degree we check is zero
    d := dim(R) + max(F) + 1;
    -- Compute Tor^R_d(M,k)
    G := resolution(F,LengthLimit => (d - min(F)));
    T := tensor(G,k);
    
    -- If true, then M is perfect; otherwise, M is not perfect over R
    HH_d(T) == 0
)

isPerfect(Module) := Boolean => (M) -> (
    isPerfect(complex(M))
)

---------------------------------------------------------------
-- Compute the support variety of a complex
---------------------------------------------------------------


--auxiliary functions

mapwithvars = method()
mapwithvars(List,Matrix,RingMap) := Matrix => (k,Mat,QtoS) -> (
    mat := QtoS ** Mat;
    S := target QtoS;
    Q := source QtoS;
    list2 := take(S_*,#Q_* - #S_*);
    o := apply(pack(2,mingle(k_0,list2)), w -> (w_1)^(w_0));
    product(o)*mat
    )

degreeij = method()
degreeij(HashTable,List,RingMap,HashTable) := Matrix => (L,degs,QtoS,ranks) -> (
    
    i := degs_0;--starting point
    j := degs_1;--ending point
    
    starting := rank(ranks#i);
    ending := rank(ranks#j);
    
    S := target QtoS;
    
    if (i > (j+1)) then map(S^ending, S^starting,0)  --replaces the negative differentials with zero
    else (
	mykeys := select(keys L, 
	    k -> (k_1 == i) and (2*sum(k_0) - 1 + k_1) == j);
--	w := apply(mykeys, k -> {k,L#k});
	sum(apply(mykeys, k -> mapwithvars(k,L#k,QtoS)))
   )
)




exts = method( );

exts(Module) := List => Y -> (
	X := complex(Y);
	R := ring X;
	I := ideal R;
	Q := ring I;
	k := coefficientRing Q;
	Pi := resolutionMap(restrict(X,Q));
	M := source Pi;
	H := higherHomotopies(flatten entries gens I, Pi,floor((length M + 1)/2));
	mu := numgens I;
	Qvars := Q_*;
	a := getSymbol "a";
	S := k(monoid[(Qvars | toList(a_1..a_mu))]);
	--Produces a polynomial ring with twice as many variables as R.  
	--The peculiar notation in the previous two lines
	--is required to ensure that the variables of S are hidden from the user.
	--In particular, the variables in Q_* are
	--still recognized as variables of Q and not S, 
	--and the code will not break if the variables in Q happen to be called
	--old bad code:
--	a := getSymbol"a";
--	S := Q[a_1 .. a_mu];
    	QtoS := map(S,Q,drop(S_*,-mu));
	T := S/ideal drop(S_*,-mu);
	odds := select(toList(min M .. max M), o -> odd(o));
	evens := select(toList(min M .. max M), o -> even(o));
	toeven := matrix table(evens, odds, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
	toodd := matrix table(odds, evens, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
    	return {toeven,toodd}
	)





--support variety
supportVariety = method( TypicalValue => Ideal,
                         Options => { Strategy => RankVarietyFast } );

supportVariety(Complex) := Ideal => opts -> (X) -> (
    if opts.Strategy === RankVariety then (
	R := ring X;
	I := ideal R;
	Q := ring I;
	k := coefficientRing Q;
	Pi := resolutionMap(restrict(X,Q));
	M := source Pi;
	H := higherHomotopies(flatten entries gens I, Pi,floor((length M + 1)/2));
	mu := numgens I;
	Qvars := Q_*;
	a := getSymbol "a";
	S := k(monoid[(Qvars | toList(a_1..a_mu))]);
	--Produces a polynomial ring with twice as many variables as R.  
	--The peculiar notation in the previous two lines
	--is required to ensure that the variables of S are hidden from the user.
	--In particular, the variables in Q_* are
	--still recognized as variables of Q and not S, 
	--and the code will not break if the variables in Q happen to be called
	--old bad code:
--	a := getSymbol"a";
--	S := Q[a_1 .. a_mu];
    	QtoS := map(S,Q,drop(S_*,-mu));
	T := S/ideal drop(S_*,-mu);
	odds := select(toList(min M .. max M), o -> odd(o));
	evens := select(toList(min M .. max M), o -> even(o));
	toeven := matrix table(evens, odds, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
	toodd := matrix table(odds, evens, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
    	toodd = compress toodd;
	return radical minors(rank ker toeven, toodd)
	);

    if opts.Strategy === RankVarietyFast then (
	R = ring X;
	I = ideal R;
	Q = ring I;
	k = coefficientRing Q;
	Pi = resolutionMap(restrict(X,Q));
	M = source Pi;
	H = higherHomotopies(flatten entries gens I, Pi,floor((length M + 1)/2));
	mu = numgens I;
	Qvars = Q_*;
	a = getSymbol "a";
	S = k(monoid[(Qvars | toList(a_1..a_mu))]);
	--Produces a polynomial ring with twice as many variables as R.  
	--The peculiar notation in the previous two lines
	--is required to ensure that the variables of S are hidden from the user.
	--In particular, the variables in Q_* are
	--still recognized as variables of Q and not S, 
	--and the code will not break if the variables in Q happen to be called
	--old bad code:
--	a := getSymbol"a";
--	S := Q[a_1 .. a_mu];
    	QtoS = map(S,Q,drop(S_*,-mu));
	T = S/ideal drop(S_*,-mu);
	odds = select(toList(min M .. max M), o -> odd(o));
	evens = select(toList(min M .. max M), o -> even(o));
	toeven = matrix table(evens, odds, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
	toodd = matrix table(odds, evens, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
    	r := rank ker toeven;
	toodd = compress toodd;
	toodd = transpose compress transpose toodd;
	N := binomial(rank source toodd,r)*binomial(rank target toodd,r);
	(if (100000 > 0.01*N) and (0.01*N > 10000) then N = ceiling(0.01*N) else N = min(N,2000));
    	return ideal mingens chooseGoodMinors(N,r,toodd)
	);

    
    if opts.Strategy === Koszul then (
        R = ring X;
        K := complex(R^1/ideal vars R);
        E := extKoszul(K,X);
        return radical ann(E)
    )
)

supportVariety(Module) := Ideal => opts -> (M) -> (
    supportVariety(complex(M), Strategy => opts.Strategy)
)

supportVariety(Complex,Complex) := Ideal => opts -> (X,Y) -> (
    if not(ring X == ring Y) then error "expected complexes over the same ring" else radical ann extKoszul(X,Y)
)



supportMatrices = method();
supportMatrices(Complex) := Ideal => X -> (
    R := ring X;
    I := ideal R;
    Q := ring I;
    k := coefficientRing Q;
    Pi := resolutionMap(restrict(X,Q));
    M := source Pi;
    H := higherHomotopies(flatten entries gens I, Pi,floor((length M + 1)/2));
    mu := numgens I;
    Qvars := Q_*;
    a := getSymbol "a";
    S := k(monoid[(Qvars | toList(a_1..a_mu))]);
    QtoS := map(S,Q,drop(S_*,-mu));
    T := S/ideal drop(S_*,-mu);
    odds := select(toList(min M .. max M), o -> odd(o));
    evens := select(toList(min M .. max M), o -> even(o));
    toeven := matrix table(evens, odds, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
    toodd := matrix table(odds, evens, (j,i) -> degreeij(H, {i,j}, QtoS, M.module)) ** T;
    {toeven, toodd}
)

supportMatrices(Module) := Ideal => X -> (supportMatrices(complex(X)))

---------------------------------------------------------------
-- Check if X is built by G
---------------------------------------------------------------
isBuilt = method( TypicalValue => Boolean ,
                  Options => { FiniteLength => false } );

isBuilt(Complex,Complex) := Boolean => opts -> (X,G) -> (
    if not(ring X === ring G) then return "expected complexes over the same ring";
    
    -- Check if the complexes are perfect
    perfectX := isPerfect(X);
    perfectG := isPerfect(G);
    if (perfectG and not perfectX) then return false;
    
    -- Check the 'classical' support of the homologies over the ring
    annH := (C) -> (
        (lo,hi) := concentration C;
        intersect apply(apply(toList(lo..hi),n -> HH_n(C)),ann)
    );
    answerSuppH := isSubset(annH G ,radical annH X);
    if not answerSuppH then (
        return false;
    ) else (
        if (perfectG and perfectX) then return true;
    );
    
    -- Check the support variety
    if opts.FiniteLength then (
        -- When a complex has finite length, check against the residue field
        R := ring X;
        k := R^1/ideal vars R;
        E1 := extKoszul(k,X);
        E2 := extKoszul(k,G);
    ) else (
        E1 = extKoszul(X,X);
        E2 = extKoszul(G,G);
    );
    
    -- Make E1 and E2 over the same (not just iso) ring
    S1 := ring E1;
    S2 := ring E2;
    iso := map(S2,S1, gens S2);
    E1 = tensor(S2,iso,E1);
    
    answerSuppVar := isSubset(ann E2, radical ann E1);
    if not answerSuppVar then return false;
    -- If the subsets contain each other, print a warning.
    print "Warning: Need not be correct if the ring is not ci";
    return true;
)

isBuilt(Module,Module) := Boolean => opts -> (M,N) -> (
    isBuilt(complex M, complex N, FiniteLength => opts.FiniteLength)
)

isBuilt(Complex,Module) := Boolean => opts -> (X,N) -> (
    isBuilt(X,complex N, FiniteLength => opts.FiniteLength)
)

isBuilt(Module,Complex) := Boolean =>  opts -> (M,G) -> (
    isBuilt(complex M,G, FiniteLength => opts.FiniteLength)
)

---------------------------------------------------------------
-- Rectriction to scalars of modules, complexes, maps
---------------------------------------------------------------

restrict = method();

-- restrict from R = Q/I to Q
restrict(Module) := Module => (M) -> (
    R := ring M;
    
    return restrict(M,ambient R);
);

restrict(Module,Ring) := Module => (M,Q) -> (
    R := ring M;
    
    if (R === Q) then return M;
    if (M == 0) then return Q^0;
    
    if (ambient R === Q) then (
        I := kernel(map(R,Q,flatten entries vars R));
        
        pM := lift(presentation M,Q);
        return cokernel ( (Q^1/I) ** pM );
    );
    
    -- if R is constructed from Q by also adjoining variables
    -- we construct: A = Q[mons] and B = A/I = R
    B := flattenRingOver(R,Q);
    I = image presentation B;
    A := ring I;
    phi := map(B,R); -- isomorphism by construction
    mons := gens(A,CoefficientRing => Q);
    
    -- M viewed as a module over A
    pM = lift(presentation tensor(phi,M),A);
    MA := cokernel ( (A^1/I) ** pM );
    
    b := basis(MA,Variables => mons,SourceRing => Q);
    return coimage b
)

restrict(Matrix) := Matrix => (f) -> (
    R := ring f;
    
    return restrict(f,ambient R);
);

restrict(Matrix,Ring) := Matrix => (f,Q) -> (
    M := f.source;
    N := f.target;
    R := ring f;
    
    if (R === Q) then return f;
    
    if (ambient R === Q) then (
        -- R-complexes containing the modules and their presentation
        F := cone(resolutionMap(complex(M),LengthLimit=>1));
        G := cone(resolutionMap(complex(N),LengthLimit=>1));
        
        -- extend the map to the presentation of the modules
        g := extend(G,F,map(G_0,F_0,f));
        
        -- lift the ring
        I := kernel(map(R,Q,flatten entries vars R));
        
        -- add relations of R to the presentations
        lF := complex({(Q^1/I) ** lift(F.dd_2,Q)});
        lG := complex({(Q^1/I) ** lift(G.dd_2,Q)});
        
        -- create lifted/induced complex map lF -> lG only in degree 0
        h := map(lG,lF,hashTable{0 => map(lG_0,lF_0,(Q^1/I) ** lift(g_1,Q),Degree => degree g_1)});
        
        return HH_0 h
    );
    
    -- if R is constructed from Q by also adjoining variables
    -- we construct: A = Q[mons] and B = A/I = R
    B := flattenRingOver(R,Q);
    I = image presentation B;
    A := ring I;
    phi := map(B,R); -- isomorphism by construction
    mons := gens(A,CoefficientRing => Q);
    
    -- B-complexes containing the modules and their presentation
    F = cone(resolutionMap(complex(tensor(phi,M)),LengthLimit=>1));
    G = cone(resolutionMap(complex(tensor(phi,N)),LengthLimit=>1));
    -- extend the map to the presentation of the modules
    g = extend(G,F,map(G_0,F_0,tensor(phi,f)));
    
    -- lift to presentation over A
    lF = complex({(A^1/I) ** lift(F.dd_2,A)});
    lG = complex({(A^1/I) ** lift(G.dd_2,A)});
    -- create lifted/induced complex map g: lF -> lG only in degree 0
    h = map(lG,lF,hashTable{0 => map(lG_0,lF_0,(A^1/I) ** lift(g_1,A),Degree => degree g_1)});
    -- map over A
    fA := HH_0 h;
    
    -- basis of target/source over Q
    bM := basis(fA.source,Variables => mons,SourceRing => Q);
    bN := basis(fA.target,Variables => mons,SourceRing => Q);
    
    -- create matrix over Q using fA and basis bM and bN
    L :=  transpose entries(fA*bM);
    Lcoeff := apply(L,c -> (
        flatten apply(toList(0..#c-1),n -> (
            coeff := coefficients(c_n,Monomials => delete(0_A,(entries bN)_n));
            apply(flatten entries coeff#1,d -> lift(d,Q))
        ))
    ));
    
    -- map M -> N over Q
    return map(coimage bN,coimage bM,transpose Lcoeff)
)

restrict(Complex) := Complex => (X) -> (
    R := ring X;
    
    return restrict(X,ambient R);
);

restrict(Complex,Ring) := Complex => (X,Q) -> (
    a := min X;
    b := max X;
    
    -- If the complex is concentrated in one degree, just restrict that module
    if (a == b) then return complex(restrict(X_a,Q),Base => a);
    
    -- otherwise lift all differentials
    L := apply(toList(a+1..b),i -> restrict(X.dd_i,Q));
    complex(L,Base => a)
)

restrict(ComplexMap) := ComplexMap => (f) -> (
    R := ring f;
    
    return restrict(f,ambient R);
);

restrict(ComplexMap,Ring) := ComplexMap => (f,Q) -> (
    X := f.source;
    Y := f.target;
    
    lo := max(min X,min Y);
    hi := min(max X,max Y);
    
    rX := restrict(X,Q);
    rY := restrict(Y,Q);
    
    map(rY,rX,hashTable apply(toList(lo..hi),i -> {i,restrict(f_i,Q)}))
)

flattenRingOver = method();
flattenRingOver(Ring,Ring) := Ring => (B,A) -> (
    -- Create list of all intermediate rings.
    rngs := append(B.baseRings,B);
    i := position(rngs,R -> R === A);
    if i === null then error "Expected B to be constructed from A";
    rngs = drop(rngs,i);
    
    -- some help functions
    degreeInRng := (var,rng) -> degree rng_(baseName var);
    pairLists := (L1,L2) -> (
        if (#L1 != #L2) then error "Expected lists of the same length";
        apply(pack(mingle(L1,L2),2),toSequence)
    );
    
    -- monoid adjoint in each step compared to the next
    mons := apply(pairLists(drop(rngs,-1),drop(rngs,1)),(R,S) -> (
        if isPolynomialRing S then ( -- variables
            if not (coefficientRing S === R) then error "Expected the coefficient ring to be the previous ring"; -- I don't think this can happen, but just to be save
            monoid S
        ) else (
            monoid {}
        )
    ));
    
    -- tensor of all monoids
    mon := fold(mons,monoid {},(a,b) -> 
        tensor(a,b,
            Join => false,
            Degrees => join(apply(vars a,v -> degreeInRng(v,B)),apply(vars b,v -> degreeInRng(v,B)))
        )
    );
    
    -- map A[..] ->> B
    --Q := if vars mon === {} then first rngs else (first rngs) mon;
    Q := (first rngs) mon;
    f := map((last rngs),Q);
    I := ker f;
    
    Q/I
);

---------------------------------------------------------------
-- auxiliary functions for homotopies
--------------------------------------------------------------


--given a key and a degree d
--constructs the key for the codomain of a map of degree d starting at the given key
compl = method()
compl(ZZ,List,List) := (MaxSize,u,L) -> (
    i := L_1;
    multideg := L_0; 
    l := u - multideg; -- new multideg
   
    test := ((i + 2*sum(multideg) - 1) > MaxSize) or (i + 2*sum(u) - 1) > MaxSize or any(l, o -> o<0) or sum(l)==0;
    
    if test then {} else {l,i + 2*sum(multideg) - 1}
    )


---------------------------------------------------------------
-- system of higher homotopies
---------------------------------------------------------------

higherHomotopies = method()

higherHomotopies(Complex) := X -> (
    R := ring X;
    I := ideal R;
    Q := ring I;
    Pi := resolutionMap(restrict(X,Q));
    M := source Pi;
    higherHomotopies(flatten entries gens I, Pi,floor((length M + 1)/2))
    )

higherHomotopies(Module) := M -> higherHomotopies(complex(M))
    
higherHomotopies(List,ComplexMap,ZZ) := (Igens,Pi,D) -> (
    Q := ring Igens_0;
    M := source Pi;
    Y := target Pi;
    K := cone(Pi)[1];
    conemap := map(M,K,id_M | map(M,Y[1],0));
--    mapfromMtoK := map(K,M, id_M || map(Y[1],M,0));
    N := #Igens;
    
    fmaps := apply(Igens, f -> map(K,M, f*id_M || map(Y[1],M,0)));
    gennullhoms := apply(fmaps, f -> complex nullhomotopy chainComplex f);
    
    H := new MutableHashTable;--H has maps with target M
    Haux := new MutableHashTable;--Haux has maps with target K
    
    --setting up homotopies of degree 1 
    e := expo(N,1);
    
    scan(flatten table(e,toList(min M .. max M), (a,j) -> {a,j}), 
	k -> (Haux#k = (gennullhoms_(position(k_0, o -> o==1)))_(k_1)));
    
    scan(flatten table(e,toList(min M .. max M), (a,j) -> {a,j}), 
	k -> (H#k = conemap_(k_1+1) * (gennullhoms_(position(k_0, o -> o==1)))_(k_1)));
    
    S := new MutableHashTable;
    
    allmaps := {};
    nullhomotopies := {};   
    
    for d from 2 to D do (
	e = expo(N,d);
	--S is an auxiliary hashtable
	S = new MutableHashTable from flatten table(
	    e, toList(min M .. max M), (w,i) -> ({w,i},map(K_(i+2*d-2),M_i,0))
	    );
	
	scan(keys H ** e, P -> (
		k := P_0;
		i := k_1;
		u := P_1;
		v := compl(max M,u,k);
		if v != {} then S#{u,i} = S#{u,i} + (Haux#v * H#k)));
       
       allmaps = apply(e, w -> (
           maps := apply(toList((min M) .. (max M)), i -> - S#{w,i});
           map(K[2*d-2], M, maps)
           )
       );  
 
       nullhomotopies = apply(allmaps, o -> complex nullhomotopy chainComplex o);

       scan( toList(0 .. (#e - 1)) ** toList(min M .. max M - 2*d + 2), W -> (
           j := W_0;
	   w := e_j;
           i := W_1;
           Haux#{w,i} = (nullhomotopies_j)_i;
           H#{w,i} = conemap_(i + 2*d - 1) * (nullhomotopies_j)_i	   
           )
       );
   );--end of for
        
    e = (expo(N,0))_0;--making degree 0 stuff
    scan(toList((min M + 1) .. max M), i -> H#{e,i} = M.dd_i);
--    scan(toList((min M + 1) .. max M), i -> Haux#{e,i} = mapfromMtoK_(i-1) * M.dd_i);
    
    hashTable pairs H
);



---------------------------------------------------------------
-- complete ext over non-ci
---------------------------------------------------------------
extKoszul = method( TypicalValue => Module );
    
--Options => { ResidueField => false }

extKoszul(Module,Module) := (M,N) -> extKoszul(complex(M), complex(N));
    
extKoszul(Complex,Complex) := (M,N) -> (
    B := ring M;
    if not(B === ring(N)) then error "expected complexes over the same ring";
    if not isCommutative B
    then error "'Ext' not implemented yet for noncommutative rings";
    if not isHomogeneous B
    then error "'Ext' received modules over an inhomogeneous ring";
    if ((not isHomogeneous M) or (not isHomogeneous N))
    then error "received an inhomogeneous complex";
    
    p := presentation B;
    A := ring p;
    I := trim ideal p;
    n := numgens A;
    c := numgens I;
    f := apply(c, i -> I_i);
    
    -- Construct ring of cohomological operators (over field)
    K := coefficientRing A;
    X := getSymbol "X";
    S := K(monoid[X_1 .. X_c, toSequence gens A,
           Degrees => { apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
                        apply(0 .. n-1, j -> prepend( 0,   degree A_j))},
           Heft => {-2,1} ]);
    -- Natural inclusion A -> S
    toS := map(S,A,apply(toList(c .. c+n-1), i -> S_i),DegreeMap => prepend_0);
    
    if (M == 0 or N == 0) then return S^0;
    
    Pi := resolutionMap(restrict(M,A));
    C := source Pi;
    homotopies := higherHomotopies(f, Pi,floor((length C + 1)/2));
    -- Construct Cstar = (S \otimes_A C)^\natural
    degreesC := toList(min C .. max C);
--     degreesC := toList(min(C)..max(C));
    Cstar := S^(apply(degreesC,i -> toSequence apply(degrees C_i, d -> prepend(i,d))));
    
    -- Construct the (almost) differential Delta: Cstar -> Cstar[-1] that combines the homotopies and multiplication by X_i
    -- We omit the sign (-1)^(n+1) which would ordinarily be used, which does not affect the homology.
    
    -- Return X^n = X_0^{n_0} *...* X_(c-1)^{n_{c-1}} for a list of integers n
    prodX := o -> product toList(apply(pairs o, i -> S_(i_0)^(i_1)));
    
    -- Create a matrix for each entry of homotopies
    r := rank Cstar;
    ranksC := apply(degreesC, o -> rank(C_o));
    
    matrixfromblocks := (M) -> fold((a,b) -> a || b,apply(M, w -> fold((a,b) -> a | b, w)));
    makematrix := (L,M) -> (
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
    
    DeltaCmatrix := sum(apply(select(keys homotopies, i -> homotopies#i != 0), 
	    i -> prodX(i_0)*toS(makematrix(i,homotopies#i))));
    DeltaC := map( Cstar,
                  Cstar, 
                  transpose DeltaCmatrix,
                  Degree => { -1, degreeLength A:0 });

    -- Rewrite N as a graded S-module D with a degree -1 map
    degreesN := toList((min N) .. (max N));
    Ndelta := apply(drop(degreesN,1), i -> N.dd_i);
    Nmods := apply(degreesN, i -> tensor(S,toS,restrict(N_i,A))); -- take them from Nmatrix? Might be faster when N a complex
    Nmatrix := apply(Ndelta, f -> tensor(S,toS,restrict(f,A)));
    Nsize := apply(Nmods,numgens);
    Ntable := table(#degreesN,#degreesN, 
	(p,q) -> if (p == (q-1)) then Nmatrix_p else map(S^(Nsize_p),S^(Nsize_q),0));
    
    DeltaNmatrix := matrixfromblocks Ntable;
    Ngraded := fold((a,b) -> a ++ b,Nmods);
    DeltaN := map(Ngraded,Ngraded,DeltaNmatrix);
    
    SignIdCstar := diagonalMatrix flatten toList apply(pairs(ranksC), 
	w -> if even(w_0) then apply(toList(1 .. w_1), o -> -1) else apply(toList(1 .. w_1), o -> 1));

    SignIdCstar = promote(SignIdCstar, S); 
    
    DeltaBar := SignIdCstar ** DeltaN + DeltaC ** id_Ngraded;

    prune homology(DeltaBar, DeltaBar)
)


---------------------------------------------------------------
-- under construction
---------------------------------------------------------------
--not exported, auxiliary function to build non-proxy small modules
findgs = method( TypicalValue => Ideal );
findgs(RingElement) := Ideal => f -> (
    Q := ring f;
    R := Q/ideal(f);
    m := ideal vars R;
    ideal append({f},lift(inhomogeneousSystemOfParameters(m,R),Q))
)
findgs(List) := Ideal => L -> (
    Q := ring L_0;
    R := Q/ideal(L);
    m := ideal vars R;
    ideal append(L,lift(inhomogeneousSystemOfParameters(m,R),Q))
)

--not exported, auxiliary function to build non-proxy small modules
makemap = method();
makemap(Ideal,Ideal) := Matrix => (I,J) -> (
    Q := ring I;
    k := coefficientRing Q;
    m := ideal vars Q;
    A := inducedMap(J/(m*J),I/(m*I));
    matrix apply(entries A, i -> apply(i,j -> lift(j,k)))
)

nonProxySmall = method();
nonProxySmall(Ideal) := Ideal => I -> (
    listf := flatten entries gens I;
    if isRegularSequence listf then error "all modules over a ci are proxy small";
    Q := ring I;
    f := first listf;
    newgs := findgs(f);
    L := {makemap(I,newgs)};
    G := {newgs};
    kers := intersect(apply(L,ker));
    g := f;
    while kers != 0 do (
    g = sum(apply(pack(2,mingle(apply(first entries transpose gens kers, o -> promote(o,Q)),listf)),product));
    newgs = findgs(g);
    L = append(L,makemap(I,newgs));
    G = append(G,newgs);
    kers = intersect(apply(L,ker))
    );
    M := (Q^1/I) ** Q/I;
    N := (Q^1/I) ** Q/I;
    w := select(1,G, o -> (N = (Q^1/o)**(Q/I); not isBuilt(M,N)));
    if w == {} then error "none found" else return w_0
)
nonProxySmall(Ring) := Module => R -> (
    I := ideal R;
    Q := ambient R;
    (Q^1/nonProxySmall(I)) ** R
    )








-----------------------------------------------------------
-----------------------------------------------------------
-- Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

doc ///
    Key
        ThickSubcategories
    Headline
        A package for computations related to finite building of complexes
    Description
        Text
            A full subcategory of the derived category ${\rm D}(R)$ is {\em thick} if it is triangulated and closed under direct summands. For every complex $X$ there exists a smallest thick subcategory containing $X$. An inductive construction of the thick subcategory is given by [BvdB03]. A complex $X$ {\em finitely builds} a complex $Y$, if $Y$ lies in the smallest thick subcategory containing $X$. The method {\tt isBuilt} checks whether $X$ finitely builds $Y$, and the method {\tt level} computes the number of steps required $X$ to build $Y$.
            
            The ring, viewed as a complex in degree 0, finitely builds every finitely generated module of finite projective dimension, and the level is the projective dimension.
    
            {\bf References}
            
            [BvdB03] Alexey I. Bondal and Michel van den Bergh, {\em Generators and representability of functors in commutative and noncommutative geometry}, Mosc. Math. J. {\bf 3} (2003), no.~1, 1–36, 258. 
            
            [Chr98] J. Daniel Christensen. {\em Ideals in triangulated categories: phantoms, ghosts and skeleta}, Adv. Math., 136(2):284–339, 1998.
///

doc ///
    Key
        ghost
        (ghost, Complex, Complex)
        (ghost, Complex, Complex, List)
        (ghost, Complex)
        (ghost, Complex, List)
    Headline
        constructs a ghost map
    Usage
        ghost(G,X)
        ghost(G,X,L)
        ghost X
        ghost(X,L)
    Inputs
        X:Complex
        G:Complex
        n:ZZ
        L:List
    Outputs
        :ComplexMap
            a map with source $X$ that is ghost with respect to $G$
    Description
        Text
            A map $X \to Y$ is ghost with respect to $G$ if any composition $G \to X \to Y$ is zero. 
        Example
            needsPackage "Complexes";
            R = QQ[x]
            X = complex(R^1/ideal(x^2))
            G = freeResolution(R^1/ideal(x))
            f = ghost(G,X)
            (prune HH_0 Hom(G,f)) == 0
        Text
            When a list of integers is given then it returns a map that is ghost with respect to $G[-n]$ for every integer $n$ in the list L.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex({map(R^1/ideal(x^2),R^1/ideal(x*y),{{x}}),map(R^1/ideal(x*y),R^1/ideal(y^2),{{x}})})
            G = freeResolution(R^1/ideal(y^2))
            f = ghost(G,X,{0,1})
            (prune HH_0 Hom(G,f)) == 0
            (prune HH_1 Hom(G,f)) == 0
        Text
            For one complex $X$, this method returns a ghost map with source $X$ with respect to the ring.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex(R^1/ideal(x*y))
            f = ghost(X)
            (prune HH_0 f) == 0
        Text
            When additionally a list of integers is given, then it returns a map that is ghost with respect to $R[-n]$ for every integer $N$ in the List L
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex(R^1/ideal(x*y)) ++ complex(R^1/ideal(x*y))[-2]
            f = ghost(X,{0,1})
            HH_0 f == 0
            HH_1 f == 0
            HH_2 f == 0
    Caveat
        This method only works if $G$ is a complex of free modules. 
///

doc ///
    Key
        coghost
        (coghost, Complex, Complex)
        (coghost, Complex, Complex,List)
        (coghost, Complex)
        (coghost, Complex,List)
    Headline
        constructs a coghost map
    Usage
        coghost(G,X)
        coghost(G,X,L)
        coghost X
        coghost(X,L)
    Inputs
        X:Complex
        G:Complex
        L:List
    Outputs
        :ComplexMap
            a map with target $X$ that is coghost with respect to $G$
    Description
        Text
            A map $W \to X$ is coghost with respect to $G$ if any composition $W \to X \to G$ is zero. 
        Example
            needsPackage "Complexes";
            R = QQ[x]
            X = freeResolution(R^1/ideal(x^2))
            G = complex(R^1/ideal(x))
            f = coghost(G,X)
            (prune HH_0 Hom(f,G)) == 0
        Text
            When a list of integers is given then it returns a map that is coghost with respect to $G[n]$ for every integer $n$ in the list L.
        Example
            needsPackage "Complexes";
            R = QQ[x]
            X = freeResolution(R^1/ideal(x^2))
            G = complex(R^1/ideal(x))
            f = coghost(G,X,{0,-1})
            (prune HH_0 Hom(f,G)) == 0
            (prune HH_(-1) Hom(f,G)) == 0
        Text
            For one complex $X$, this method returns a coghost map with target $X$ with respect to the ring.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = freeResolution(R^1/ideal(x*y))
            f = coghost(X)
            (prune HH_0 Hom(f,complex R^1)) == 0
    Caveat
        This method only works if $X$ is a complex of free modules. 
///

doc ///
    Key
        level
        (level, Complex, List)
        (level, Complex, Complex, List)
        (level, Module, List)
        (level, Module, Module, List)
        (level, Module, Complex, List)
        (level, Complex, Module, List)
    Headline
        computes the level of a complex with respect to another complex, or the ring by default
    Usage
        level(X,L)
        level(G,X,L)
        level(M,L)
        level(N,M,L)
        level(N,X,L)
        level(G,M,L)
    Inputs
        X:Complex
        G:Complex -- if no G is provided, G is assumed to be the underlying ring
        M:Module -- M is replaced with the corresponding complex
        N:Module -- N is replaced with the corresponding complex
        L:List
    Outputs
        :ZZ
            the level of X with respect to {G[-n] | n in L}
    Description
        Text
            Computes the level of the second complex with respect to the first complex. 
        Text
            When the input is one complex, then it computes the level with respect to the ring. 
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            F = koszulComplex {x^2,x*y,y^2}
            level(F,{0,1,2,3})
        Text
            When the input is one module, then it computes the level of the module viewed as a complex concentrated in degree 0. If enough suspensions are allowed, then the output is precisely the projective dimension $+1$. 
        Example
            R = QQ[x,y]
            M = R^1/ideal(x,y)
            level(M,toList(0..3))
        Text
            When the input consists of two complexes (or modules or one complex and one module), then it computes the level of the second complex with respect to the first. 
        Example
            R = QQ[x]
            M = R^1/ideal(x)
            N = R^1/ideal(x^4)
            level(M,N,{0})
    Caveat
        Only returns the correct answer if both arguments are perfect.
    SeeAlso
        ghost
        coghost
///

doc ///
    Key
        MaxLevelAttempts
        [level,MaxLevelAttempts]
    Headline
        stop when this number is reached
    Usage
        level(..., MaxLevelAttempts => 10)
    Description
        Text
            When computing the level of a complex, a sequence of ghost maps is constructed. The level is the smallest number for which the composition of the ghost maps is zero. This option stops the computation after the given number of steps. 
        Example
            R = QQ[x,y]
            M = R^1/ideal(x,y)
            level(M,{0,1},MaxLevelAttempts => 5)
            level(M,{0,1,2},MaxLevelAttempts => 5)
    SeeAlso
        level
///

doc ///
    Key
        [level,LengthLimit]
    Headline
        compute the resolution of the complex of at most this length
    Usage
        level(..., LengthLimit => 10)
    Description
        Text
            To compute the level of a complex, the level of its free resolution is computed. 
        Example
            R = QQ[x]/(x^2)
            M = R^1/ideal(x)
            level(M,toList(0..4),LengthLimit => 4)
            level(M,toList(0..5),LengthLimit => 5)
    SeeAlso
        level
///

doc ///
    Key
        LengthLimitGenerator
        [level,LengthLimitGenerator]
    Headline
        compute the resolution of the generator of at most this length
    Usage
        level(..., LengthLimitGenerator => 5)
    Description
        Text
            To compute the level with respect to a $G$, the level with respect to a free resolution of $G$ is computed. 
        Example
            needsPackage "Complexes";
            R = QQ[x]/(x^2)
            G = R^1/ideal(x)
            f1 = map(R^1,R^1,matrix{{x}})
            f2 = map(source f1,,matrix{{x}})
            f3 = map(source f2,,matrix{{x}})
            X = complex{f1,f2,f3}
            level(G,X,{0,1,2},LengthLimitGenerator => 2)
            level(G,X,{0,1,2},LengthLimitGenerator => 3)
    SeeAlso
        level
///

doc ///
    Key
        [level,Strategy]
    Headline
        choose the strategy used to compute level
    Usage
        level(G,X, LengthLimitGenerator => "ghost")
        level(G,X, LengthLimitGenerator => "coghost")
    Description
        Text
            The default value is "ghost".
    SeeAlso
        coghost
        ghost
        level
///

doc ///
    Key
        isPerfect
        (isPerfect, Complex)
        (isPerfect, Module)
    Headline
        determines whether a complex is perfect over the ring it is defined over
    Usage
        isPerfect(X)
        isPerfect(M)
    Inputs
        X:Complex
        M:Module -- M is replaced with the corresponding complex
    Outputs
        :Boolean
            true if the complex is perfect over the ring it is defined over and false otherwise
    Description
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            m = ideal(vars R);
            k = complex(R^1/m);
            isPerfect(k)
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            m = ideal(vars R);
            k = complex(R^1/m)[-2];
            isPerfect(k)
        Example
            needsPackage "Complexes";
            R = QQ[x,y];
            m = ideal(vars R);
            k = complex(R^1/m)[2];
            isPerfect(k)    
        Example
            R = ZZ/2[x,y]/ideal(x^2,y^2);
            needsPackage("Complexes");
            m = ideal(vars R);
            k = complex(R^1/m);
            isPerfect(k)
        Example
            needsPackage "Complexes";
            R = ZZ/2[x,y]/ideal(x^2,y^2);
            m = ideal(vars R);
            k = complex(R^1/m)[-2];
            isPerfect(k)
        Example
            needsPackage "Complexes";
            R = ZZ/2[x,y]/ideal(x^2,y^2);
            m = ideal(vars R);
            k = complex(R^1/m)[2];
            isPerfect(k)         
///

doc ///
    Key
        supportVariety
        (supportVariety, Complex)
        (supportVariety, Module)
    Headline
        computes the support variety of a complex
    Usage
        supportVariety(X)
        supportVariety(M)
    Inputs
        X:Complex
        M:Module
    Outputs
        :Ideal
            The ideal whose vanishing set is the support variety.
    Description
        Text
            TODO
    Caveat
        Only returns a correct answer if the input is a module or a complex of finite length homology using the optional input {\tt FiniteLength}.
///

doc ///
    Key
        FiniteLength
        [isBuilt,FiniteLength]
    Headline
        simplify computation when the input has finite length homology
    Usage
        isBuilt(..., FiniteLength => false)
    Description
        Text
            For a complex with finite length homology $X$ the support variety can be computed via the support of the ext module ${\rm Ext}(k,X)$ where $k$ is the residue field.
    SeeAlso
        isBuilt

///

doc ///
    Key
        isBuilt
        (isBuilt, Complex, Complex)
        (isBuilt, Module, Module)
        (isBuilt, Module, Complex)
        (isBuilt, Complex, Module)
    Headline
        determines whether the first complex can be finitely built by the second
    Usage
        isBuilt(X,Y)
        isBuilt(M,N)
        isBuilt(M,Y)
        isBuilt(X,N)
    Inputs
        X:Complex
        Y:Complex
        M:Module -- M is replaced with the corresponding complex
        N:Module -- N is replaced with the corresponding complex
    Outputs
        :Boolean
            true if Y can be finitely built by X, and false if not
    Description
        Example
            needsPackage "Complexes";
            R = QQ[x,y]/ideal(x^3,x*2*y);
            X = complex koszul matrix{{x^2,x*y}}
            Y = complex koszul matrix{{x,y}}
            isBuilt(X,Y)
            isBuilt(Y,X)
    Caveat
        The answer is only guaranteed to be correct if the input is a module or a complex of finite length homology using the optional input {\tt FiniteLength}.
        
        When the method returns {\tt true}, $X$ need not be built by $Y$. In the following cases {\tt true} is correct:
        
        - The ring is complete intersection, or
        
        - Y is perfect.
///

doc ///
    Key
        restrict
    Headline
        view the given object as an object over the polynomial ring
///

doc ///
    Key
        (restrict,Module,Ring)
        (restrict,Module)
    Headline
        view the module as a module over another ring
    Usage
        restrict(M)
        restrict(M,Q)
    Inputs
        M:Module
        Q:Ring
    Outputs
        :Module
            over Q (or the ambient polynomial ring)
    Description
        Text
            When no ring is given, the module is lifted to the ambient polynomial ring of the ring of the module. 
        Example
            R = QQ[x]/ideal(x^2);
            M = R^1/ideal(x);
            restrict M
        Text
            When a ring is given, the module is lifted to that ring. This only works, when the module is finitely generated over that ring. 
        Example
            Q = QQ[x]/ideal(x^3);
            R = Q/ideal(x^2);
            M = R^1/ideal(x);
            restrict(M,Q)
        Example
            Q = QQ[x];
            R = Q[y];
            M = R^1/ideal(y^2);
            restrict(R^1/ideal(y^2),Q)
///

doc ///
    Key
        (restrict,Matrix,Ring)
        (restrict,Matrix)
    Headline
        view the map as a map over another ring
    Usage
        restrict(f)
        restrict(f,Q)
    Inputs
        f:Matrix
        Q:Ring
    Outputs
        :Matrix
            over Q (or the ambient polynomial ring)
    Description
        Text
            When no ring is given, the map is lifted to the ambient polynomial ring of the ring of the map. 
        Example
            R = QQ[x]/ideal(x^2);
            f = map(R^1,R^1,{{x}})
            g = restrict f
            ring g
        Example
            R = QQ[x,y]/ideal(x*y);
            f = inducedMap(R^1/ideal(x,y),R^1/ideal(x))
            g = restrict f
            g.source
            g.target
        Example
            Q = QQ[x]/ideal(x^3);
            R = Q/ideal(x^2);
            f = map(R^1,R^1,{{x}})
            g = restrict(f,Q)
            ring g
///

doc ///
    Key
        (restrict,Complex,Ring)
        (restrict,Complex)
    Headline
        view the complex as a complex over another ring
    Usage
        restrict(C)
        restrict(C,Q)
    Inputs
        C:Complex
        Q:Ring
    Outputs
        :Complex
            over Q (or the ambient polynomial ring)
    Description
        Text
            When no ring is given, the complex is lifted to the ambient polynomial ring of the ring of the complex. 
        Example
            needsPackage "Complexes";
            R = QQ[x]/ideal(x^2);
            F = complex(R^1/ideal(x),Base => 2)
            restrict F
        Example
            needsPackage "Complexes";
            R = QQ[x,y]/ideal(x*y);
            F = freeResolution(R^1/ideal(x^2,y^2),LengthLimit => 2)
            F.dd
            G = restrict F
            G.dd
        Example
            needsPackage "Complexes";
            Q = QQ[x]/ideal(x^3);
            R = Q/ideal(x^2);
            F = complex(R^1/ideal(x),Base => 2)
            restrict(F,Q)
///


doc ///
    Key
        nonProxySmall
    	(nonProxySmall,Ring)
        (nonProxySmall,Ideal)
    Headline
        if the given ring is not a ci, constructs a module that is not proxy small
    Usage
        nonProxySmall(R)
        nonProxySmall(I)
    Inputs
        C:Ring
        I:Ideal
    Outputs
        :Module
            nonproxy small module over the given ring
    Description
        Text
            When no ring is given, the complex is lifted to the ambient polynomial ring of the ring of the complex. 
        Example
            R = QQ[x,y]/ideal(x^2,x*y)
            nonProxySmall(R)
        Text
            We can instead give an ideal $I$ in a ring $Q$, and compute a non-proxy small module over $Q/I$
        Example
            Q = QQ[x,y]
            I = ideal(x^2,x*y)
            nonProxySmall(I)
        Text
            If the given ring is a complete intersection, all modules are proxy small. 
        Example
            R = QQ[x]/ideal(x^2)
--        nonProxySmall(R)
///


doc ///
    Key
        extKoszul
        (extKoszul, Complex, Complex)
    Headline
        computes the Ext module over the polynomial ring of cohomological operators
    Usage
        extKoszul(X,Y)
    Inputs
        X:Complex
        Y:Complex
    Outputs
        :Module
            over $R[\chi_1, \ldots, \chi_c]$
    Description
        Text
            TODO
///

-----------------------------------------------------------
-----------------------------------------------------------
-- Tests
-----------------------------------------------------------
-----------------------------------------------------------

-----------------------------------------------------------
-- level
-----------------------------------------------------------


TEST ///
    R = QQ[x,y,z]
    assert(level(R^1,{0}) == 1)
///


TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    F = freeResolution (R^2)
    assert(level(F,{0}) == 1)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]/ideal(x*y*z)
    G = complex (R^2)
    F = G ++ G[1] ++ G[-1]
    assert(level(F,{-1,0,1}) == 1)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I)
    assert(level(F,{0,1,2,3}) == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I)[-3]
    assert(level(F,{3,4,5,6}) == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I^2)
    assert(level(F,{0,1,2,3}) == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y]
    G = freeResolution(R^1/ideal(x))
    X = freeResolution(R^1/ideal(x,y^2))
    assert(level(G,X,{0,1}) == 2)
///

end
