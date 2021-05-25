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
    -- Methods
    "ghost",
    "coghost",
    "level",
    "isPerfect",
    "supportVariety",
    "isBuilt",
    "nonProxySmall",
    "extKoszul",
    "findgs",
    "restrict"
}

needsPackage "Complexes"
needsPackage "Depth"
needsPackage "MinimalPrimes"
needsPackage "CompleteIntersectionResolutions"

---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-- Create the G-ghost map associated to the right G-approximation
---------------------------------------------------------------
ghost = method( TypicalValue => ComplexMap );

-- Creates a map with source X that is G-ghost in degrees <= n
ghost(Complex,Complex,ZZ) := ComplexMap => (G,X,n) -> (
    -- Input: G needs to be a complex of projective modules
    -- Check that G and X are complexes over the same ring
    R := ring G;
    if not(R === ring X) then error "expected complexes over the same ring";
    
    H := Hom(G,X);
    
    -- Collect the generators of H in the form G[-i] -> X
    generatorsInDegree := (i) -> (
        K := ker H.dd_i;
        Q := cover K;
        -- induced module map Q -> H_i
        h := inducedMap(H_i,K)*map(K,Q,id_Q);
        
        -- get R^[-i] -> H from the jth component of Q
        pickGenerator := (j) ->  map(H,(complex R^1)[-i],k -> if k==i then map(H_i,R^1,h*(id_Q)_{j}));
        -- from R^1[-i] -> H get G[-i] -> X
        generatorToMorphism := (f) -> map(X,G[-i],(homomorphism f)[-i],Degree => 0);
        
        apply(toList(0..(rank Q-1)),j -> generatorToMorphism(pickGenerator j))
    );
    
    L := flatten apply(toList((min H)..n),generatorsInDegree);
    
    f := fold((a,b) -> a | b,L);
    canonicalMap(cone(f),X)
)

ghost(Complex,Complex) := ComplexMap => (G,X) -> (
    ghost(G,X,min G + max X)
)

-- Creates a map with source X that is R-ghost in degrees <= n
ghost(Complex,ZZ) := ComplexMap => (X,n) -> (
    R := ring X;
    
    -- Construct the R-approximation of X
    Q := fold((a,b) -> a ++ b,complex R^0,apply(toList((min X)..n),i -> complex(cover ker X.dd_i)[-i]));
--     Q := complex R^0;
--     for i from min X to n do Q = Q ++ complex(cover ker X.dd_i)[-i];
    
    -- Construct map Q -> X
    fun := i -> if (i >= min X or i <= n) then inducedMap(X_i,ker X.dd_i)*map(ker X.dd_i,Q_i,id_(Q_i)) else map(R^0,X_i);
    
    -- Return the map X -> G
    canonicalMap(cone(map(X,Q,fun)),X)
)

-- Creates an R-ghost map with source X
ghost(Complex) := ComplexMap => (X) -> (
    ghost(X,max HH X)
)

---------------------------------------------------------------
-- Create the G-coghost map associated to the left G-approximation
---------------------------------------------------------------
coghost = method( TypicalValue => ComplexMap );

coghost(Complex,Complex) := ComplexMap => (G,X) -> (
    -- Check that G and X are complexes over the same ring
    R := ring G;
    if not(R === ring X) then error "expected complexes over the same ring";
    
    H := Hom(X,G);
    
    -- Collect the generators of H of the form X -> G[i]
    generatorsInDegree := (i) -> (
        K := ker H.dd_i;
        Q := cover K;
        -- induced module map Q -> H_i
        h := inducedMap(H_i,K)*map(K,Q,id_Q);
        
        -- get R^[-i] -> H from the jth component of Q
        pickGenerator := (j) ->  map(H,(complex R^1)[-i],k -> if k==i then map(H_i,R^1,h*(id_Q)_{j}));
        -- from R^1[-i] -> H get X -> G[i]
        generatorToMorphism := (f) -> map(G[i],X,(homomorphism f),Degree => 0);
        
        apply(toList(0..(rank Q-1)),j -> generatorToMorphism(pickGenerator j))
    );
    
    L := flatten apply(toList((min H)..(max H)),generatorsInDegree);
    
    f := fold((a,b) -> a || b,L);
    canonicalMap(X[-1],cone(f))[1]
)

coghost(Complex) := ComplexMap => (X) -> (
    coghost(complex((ring X)^1),X)
)

---------------------------------------------------------------
-- Compute the level of X with respect to G
---------------------------------------------------------------
level = method( TypicalValue => ZZ,
                Options => { MaxLevelAttempts => 10,
                             LengthLimit => 10,
                             LengthLimitGenerator => 5,
                             Strategy => "ghost" } );

level(Complex,Complex) := ZZ => opts -> (G,X) -> (
    -- Check that G and X are complexes over the same ring
    if not(ring G === ring X) then error "expected complexes over the same ring";
    
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
            f = coghost(rG,rX);
            
            g = g*f;
            n = n+1;
        );
    ) else ( -- Ghost maps
        -- As long as the composition of the ghost maps g is non-zero, continue
        while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
            rX = f.target;
            f = ghost(rG,rX);
            
            -- minimize if possible
            if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
            
            g = f*g;
            n = n+1;
        );
    );
    n
)

-- Level with respect to R
level(Complex) := ZZ => opts -> (X) -> (
    rX := resolution(X, LengthLimit => opts.LengthLimit);
    n := 0;
    f := id_(rX);
    g := f;
    h := max HH X;
    i := min X;
    homogeneous := isHomogeneous X;
    -- The strategy decides whether ghost or coghost maps are used
    if (opts.Strategy == "coghost") then ( -- Coghost maps
        -- For coghost maps there is no `better' way for level wrt to R
        n = level((ring X)^1,rX, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => 0, Strategy => opts.Strategy);
    ) else ( -- Ghost maps
        -- As long as the composition of the ghost maps g is non-zero, continue
        while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
            rX = f.target;
            f = ghost(rX,h+n);
            -- minimize if possible
            if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
            
            -- The target always has zeros in degrees <= i+n, so those degrees do not play a role when testing if the map is null-homotopic
            g = f*g*inducedMap(g.source,naiveTruncation(g.source,i+n+1,));
            n = n+1;
        );
    );
    n
)

level(Module) := ZZ => opts -> (M) -> (
    X := complex(M);
    level(X, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, Strategy => opts.Strategy)
)

level(Module,Module) := ZZ => opts -> (M,N) -> (
    level(complex(M),complex(N), MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
)

level(Module,Complex) := ZZ => opts -> (M,X) -> (
    level(complex(M),X, MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
)

level(Complex,Module) := ZZ => opts -> (G,N) -> (
    level(G,complex(N), MaxLevelAttempts => opts.MaxLevelAttempts, LengthLimit => opts.LengthLimit, LengthLimitGenerator => opts.LengthLimitGenerator, Strategy => opts.Strategy)
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
supportVariety = method( TypicalValue => Ideal,
                         Options => { FiniteLength => false } );

supportVariety(Complex) := Ideal => opts -> (Y) -> (
    if opts.FiniteLength then (
        R := ring Y;
        k := complex(R^1/ideal vars R);
        E := extKoszul(k,Y);
        radical ann(E)
    ) else (
        E = extKoszul(Y,Y);
        radical ann(E)
    )
)

supportVariety(Module) := Ideal => opts -> (M) -> (
    supportVariety(complex(M), FiniteLength => opts.FiniteLength)
)

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

isBuilt(Module,Module) := Boolean => (M,N) -> (
    isBuilt(complex M, complex N)
)

isBuilt(Complex,Module) := Boolean => (X,N) -> (
    isBuilt(X,complex N)
)

isBuilt(Module,Complex) := Boolean => (M,G) -> (
    isBuilt(complex M,G)
)

---------------------------------------------------------------
-- Rectriction to scalars of modules, complexes, maps
---------------------------------------------------------------

restrict = method();

restrict(Module) := Module => (M) -> (
    R := ring M;
    
    p := presentation R;
    Q := ring p;
    I := trim ideal p;
    
    pM := lift(presentation M,Q);
    -- Both of the following work, but the second is more efficient.
--     cokernel ( pM | p ** id_(target pM) )
    cokernel ( (Q^1/I) ** pM )
)

restrict(Module,Ring) := Module => (M,Q) -> (
    R := ring M;
    
    if (R === Q) then return M;
    
    if not isQuotientOf(Q,R) then error "expected ring of module to be a quotient of second input";
    
    I := kernel(map(R,Q,flatten entries vars R));
    
    pM := lift(presentation M,Q);
--     cokernel ( pM | p ** id_(target pM) )
    cokernel ( (Q^1/I) ** pM )
)

-- This can be simplified, especially at the end. 
restrict(ModuleMap,Ring) := ModuleMap => (f,Q) -> (
    M := f.source;
    N := f.target;
    R := ring f;
    
    if (R === Q) then return f;
    
    if not isQuotientOf(Q,R) then error "expected ring of module to be a quotient of second input";
    
    -- R-complexes containing the modules and their presentation
    F := cone(resolutionMap(complex(M),LengthLimit=>1));
    G := cone(resolutionMap(complex(N),LengthLimit=>1));
    
    -- extend the map to the presentation of the modules
    g := extend(G,F,f);
    
    -- lift the ring
    I := kernel(map(R,Q,flatten entries vars R));
    
    -- lift the presenentation
    pM := lift(F.dd_2,Q);
    pN := lift(G.dd_2,Q);
    
    -- add relations of M to the lifted presentation
    -- both work, but second more efficient
--     lF := complex({pM | p ** id_(target pM)});
    lF := complex({(Q^1/I) ** pM});
    
    -- compose lifted presentation of N with the surjection Q ->> R
    -- both work, but second more efficient
--     lG := complex({(inducedMap(cokernel p,p.target) ** id_(target pN)) * pN});
    lG := complex({(Q^1/I) ** pN});
    
    -- create lifted/induced complex map g: lF -> lG only in degree 0
    h := map(lG,lF,hashTable{0 => map(lG_0,lF_0,(Q^1/I) ** lift(g_1,Q),Degree => degree g_1)});
        
    HH_0 h
)

-- This can be simplified, especially at the end. 
restrict(ModuleMap) := ModuleMap => (f) -> (
    M := f.source;
    N := f.target;
    R := ring f;
    
    -- R-complexes containing the modules and their presentation
    F := cone(resolutionMap(complex(M),LengthLimit=>1));
    G := cone(resolutionMap(complex(N),LengthLimit=>1));
    
    -- extend the map to the presentation of the modules
    g := extend(G,F,f);
    
    -- lift the ring
    p := presentation R;
    Q := ring p;
    I := trim ideal p;
    
    -- lift the presenentation
    pM := lift(F.dd_2,Q);
    pN := lift(G.dd_2,Q);
    
    -- add relations of M to the lifted presentation
    -- both work, but last more efficient
--     lF := complex({pM | p ** id_(target pM)});
    lF := complex({(Q^1/I) ** pM});
    
    -- compose lifted presentation of N with the surjection Q ->> R
    -- both work, but last more efficient
--     lG := complex({(inducedMap(cokernel p,p.target) ** id_(target pN)) * pN});
    lG := complex({(Q^1/I) ** pN});
    
    -- create lifted/induced complex map g: lF -> lG only in degree 0
    h := map(lG,lF,hashTable{0 => map(lG_0,lF_0,(Q^1/I) ** lift(g_1,Q),Degree => degree g_1)});
        
    HH_0 h
)

restrict(Complex,Ring) := Complex => (C,Q) -> (
    a := min C;
    b := max C;
    
    -- If the complex is concentrated in one degree, just restrict that module
    if (a == b) then return complex(restrict(C_a,Q),Base => a);
    
    -- otherwise lift all differentials
    -- list of restricted differentials
    L := {};
    
    for i from (a + 1) to b do (
        L = append(L,restrict(C.dd_i,Q));
    );
    
    complex(L,Base => a)
)

restrict(Complex) := Complex => (C) -> (
    a := min C;
    b := max C;
    
    -- If the complex is concentrated in one degree, just restrict that module
    if (a == b) then return complex(restrict(C_a),Base => a);
    
    -- otherwise lift all differentials
    -- list of restricted differentials
    L := {};
    
    for i from (a + 1) to b do (
        L = append(L,restrict(C.dd_i));
    );
    
    complex(L,Base => a)
)

---------------------------------------------------------------
-- complete ext over non-ci
---------------------------------------------------------------
extKoszul = method( Options => { ResidueField => false } );

extKoszul(Complex,Complex) := Module => opts -> (M,N) -> (
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
    
    if opts.ResidueField then (
        C := koszul vars A;
    ) else (
        M' := restrict(M,A); -- homogeneous
        assert isHomogeneous M'; -- is this necessary, that is is there a way that the construction could give a non-homogeneous module?    
        C = chainComplex resolution(M');
        -- keys: {J,d} where J a list of integers of length c and d the degree of the source in C
    );
    
    homotopies := makeHomotopies(matrix{f},C);
    -- Construct Cstar = (S \otimes_A C)^\natural
    degreesC := sort select(keys C, i -> class i === ZZ);
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
    
    DeltaCmatrix := sum(apply(select(keys homotopies, i -> homotopies#i != 0), i -> prodX(i_0)*toS(makematrix(i,homotopies#i))));
    DeltaC := map( Cstar,
                  Cstar, 
                  transpose DeltaCmatrix,
                  Degree => { -1, degreeLength A:0 });

    -- Rewrite N as a graded S-module D with a degree -1 map
    degreesN := toList((min N) .. (max N));
    Ndelta := apply(degreesN, i -> N.dd_i);
    Nmods := apply(degreesN, i -> tensor(S,toS,restrict(N_i,A)));
    Nmatrix := apply(Ndelta, f -> tensor(S,toS,restrict(f,A)));
    Nsize := apply(Nmods,numgens);
    Ntable := table(#Nmatrix,#Nmatrix, (p,q) -> if (p == (q-1)) then Nmatrix_(p+1) else map(S^(Nsize_p),S^(Nsize_q),0));
    
    DeltaNmatrix := matrixfromblocks Ntable;
    Ngraded := fold((a,b) -> a ++ b,Nmods);
    DeltaN := map(Ngraded,Ngraded,DeltaNmatrix);
    
    SignIdCstar := diagonalMatrix flatten toList apply(pairs(ranksC), w -> if even(w_0) then apply(toList(1 .. w_1), o -> -1) else apply(toList(1 .. w_1), o -> 1));

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
    M := Q^1/I ** Q/I;
    N := Q^1/I ** Q/I;
    w := select(1,G, o -> (N = (Q^1/o)**(Q/I); not isBuilt(M,N)));
    if w == {} then (return "none found") else return w_0
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
            
            [BvdB03] Alexey I. Bondal and Michel van den Bergh, {\em Generators and representability of functors in commutative and noncommutative geometry}, Mosc. Math. J. {\bf 3} (2003), no.~1, 1–36, 258. \break
            [Chr98] J. Daniel Christensen. {\em Ideals in triangulated categories: phantoms, ghosts and skeleta}, Adv. Math., 136(2):284–339, 1998.
///

doc ///
    Key
        ghost
        (ghost, Complex, Complex)
        (ghost, Complex, Complex, ZZ)
        (ghost, Complex)
        (ghost, Complex, ZZ)
    Headline
        constructs a ghost map
    Usage
        ghost(G,X)
        ghost(G,X,n)
        ghost X
        ghost(X,n)
    Inputs
        X:Complex
        G:Complex
        n:ZZ
    Outputs
        :ComplexMap
            a ghost map with source $X$
    Description
        Text
            This method computes a map with source $X$, that is ghost with respect to $G$. That is any pre-composition with a suspension of $G$ is zero in the derived category.
        Example
            needsPackage "Complexes";
            R = QQ[x]
            X = complex(R^1/ideal(x^2))
            G = freeResolution(R^1/ideal(x))
            f = ghost(G,X)
            (prune HH Hom(G,f)) == 0
        Text
            When additionally an integer $n$ is given, the output is a ghost map in degrees $\leq n$. 
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex({map(R^1/ideal(x^2),R^1/ideal(x*y),{{x}}),map(R^1/ideal(x*y),R^1/ideal(y^2),{{x}})})
            G = freeResolution(R^1/ideal(y^2))
            f = ghost(G,X,1)
            (prune HH_(-1) Hom(G,f)) == 0
            (prune HH_0 Hom(G,f)) == 0
            (prune HH_1 Hom(G,f)) == 0
            (prune HH_2 Hom(G,f)) == 0
        Text
            For one complex $X$, this method returns a ghost map with source $X$ with respect to the ring.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex(R^1/ideal(x*y))
            f = ghost(X)
            (prune HH f) == 0
        Text
            For a complex $X$ and an integer $n$, the method considers only the part of the complex $X$ of degree less or equal to $n$. That is it computes a map starting at $X$, that is zero in homology of degree less or equal $n$.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = complex(R^1/ideal(x*y)) ++ complex(R^1/ideal(x*y))[-2]
            f = ghost(X,1)
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
        (coghost, Complex)
    Headline
        constructs a coghost map
    Usage
        coghost X
        coghost(G,X)
    Inputs
        X:Complex
        G:Complex
    Outputs
        :ComplexMap
            a coghost map with target $X$
    Description
        Text
            This method computes a map with target $X$, that is coghost with respect to $G$. That is any post-composition with a suspension of $G$ is zero in the derived category.
        Example
            needsPackage "Complexes";
            R = QQ[x]
            X = freeResolution(R^1/ideal(x^2))
            G = complex(R^1/ideal(x))
            f = coghost(G,X)
            (prune HH Hom(f,G)) == 0
        Text
            For one complex $X$, this method returns a coghost map with target $X$ with respect to the ring.
        Example
            needsPackage "Complexes";
            R = QQ[x,y]
            X = freeResolution(R^1/ideal(x*y))
            f = coghost(X)
            (prune HH Hom(f,complex R^1)) == 0
    Caveat
        This method only works if $X$ is a complex of free modules. 
///

doc ///
    Key
        level
        (level, Complex)
        (level, Complex, Complex)
        (level, Module)
        (level, Module, Module)
        (level, Module, Complex)
        (level, Complex, Module)
    Headline
        computes the level of a complex with respect to another complex, or the ring by default
    Usage
        level(X)
        level(G,X)
        level(M)
        level(N,M)
        level(N,X)
        level(G,M)
    Inputs
        X:Complex
        G:Complex -- if no G is provided, G is assumed to be the underlying ring
        M:Module -- M is replaced with the corresponding complex
        N:Module -- N is replaced with the corresponding complex
    Outputs
        :ZZ
            the level of X with respect to G
    Description
        Text
            Computes the level of the second complex with respect to the first complex. 
        Text
            When the input is one complex, then it computes the level with respect to the ring. 
        Example
            needsPackage "Complexes";
            R = QQ[x,y,z]
            F = complex(R^0)
            level(F)
        
        Text
            When the input is one module, then it computes the level of the module viewed as a complex concentrated in degree 0. The output is precisely the projective dimension $+1$. 
        Example
            R = QQ[x,y]
            M = R^1/ideal(x,y)
            level(M)
        
        Text
            When the input consists of two complexes (or modules or one complex and one module), then it computes the level of the first complex with respect to the second. 
        Example
            R = QQ[x]
            M = R^1/ideal(x)
            N = R^1/ideal(x^4)
            level(M,N)
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
            R = QQ[x]/(x^2)
            M = R^1/ideal(x)
            level(M,MaxLevelAttempts => 4)
            level(M,MaxLevelAttempts => 5)
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
            level(M,LengthLimit => 4)
            level(M,LengthLimit => 5)
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
        level(G,X, LengthLimitGenerator => 5)
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
            level(G,X,LengthLimitGenerator => 2)
            level(G,X,LengthLimitGenerator => 3)
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
        [supportVariety,FiniteLength]
        [isBuilt,FiniteLength]
    Headline
        simplify computation when the input has finite length homology
    Usage
        supportVariety(..., FiniteLength => false)
    Description
        Text
            For a complex with finite length homology $X$ the support variety can be computed via the support of the ext module ${\rm Ext}(k,X)$ where $k$ is the residue field.
    SeeAlso
        supportVariety
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
        determines whether the first copmlex is built by the second
    Usage
        isPerfect(X,Y)
        isPerfect(M,N)
        isPerfect(M,Y)
        isPerfect(X,N)
    Inputs
        X:Complex
        Y:Complex
        M:Module -- M is replaced with the corresponding complex
        N:Module -- N is replaced with the corresponding complex
    Outputs
        :Boolean
            true if Y is built by X, and false if not
    Description
        Example
            needsPackage "Complexes";
            R = QQ[x,y]/ideal(x^3,x*2*y);
            X = complex koszul matrix{{x^2,x*y}}
            Y = complex koszul matrix{{x,y}}
            isBuilt(X,Y)
            isBuilt(Y,X)
    Caveat
        Only returns a correct answer if the input is a module or a complex of finite length homology using the optional input {\tt FiniteLength}.
        
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
        view the module as a module over an ambient ring
    Usage
        restrict(M)
        restrict(M,Q)
    Inputs
        M:Module
        Q:Ring
    Outputs
        :Module
            over Q or the polynomial ring
    Description
        Text
            When no ring is given, the module is lifted to the ambient polynomial ring of the ring of the module. 
        Example
            R = QQ[x]/ideal(x^2);
            M = R^1/ideal(x);
            restrict M
        Example
            Q = QQ[x]/ideal(x^3);
            R = Q/ideal(x^2);
            M = R^1/ideal(x);
            restrict(M,Q)
///

doc ///
    Key
        (restrict,ModuleMap,Ring)
        (restrict,ModuleMap)
    Headline
        view the map as a map over an ambient ring
    Usage
        restrict(f)
        restrict(f,Q)
    Inputs
        f:ModuleMap
        Q:Ring
    Outputs
        :ModuleMap
            over Q or the polynomial ring
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
        view the complex as a complex over an ambient ring
    Usage
        restrict(C)
        restrict(C,Q)
    Inputs
        C:Complex
        Q:Ring
    Outputs
        :Complex
            over Q or the polynomial ring
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
    assert(level(R^1) == 1)
///


TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    F = freeResolution (R^2)
    assert(level F == 1)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]/ideal(x*y*z)
    G = freeResolution (R^2)
    F = G ++ G[1] ++ G[-1]
    assert(level F == 1)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I)
    assert(level F == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I)[-3]
    assert(level F == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y,z]
    I = ideal vars R
    F = freeResolution(R^1/I^2)
    assert(level F == 4)
///

TEST ///
    needsPackage "Complexes"
    R = QQ[x,y]
    G = freeResolution(R^1/ideal(x))
    X = freeResolution(R^1/ideal(x,y^2))
    assert(level(G,X) == 2)
///

end
