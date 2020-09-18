newPackage(
    "Levels",
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
    -- Methods
    "ghost",
    "level",
    "isPerfect",
    "supportVariety",
    "isBuilt",
    "nonProxySmall"
}

needsPackage "Complexes"
needsPackage "Depth"
needsPackage "CompleteIntersectionResolutions"

---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-- This function creates the G-ghost map associated to the approximation
ghost = method();

ghost(Complex,Complex) := (G,X) -> (
    R := ring G;
    
    H := Hom(G,X);
    
    -- Collect the generators of H: maps f_i: G[n_i] -> X
    L := {};
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
    f := fold((a,b) -> a | b,L);
    canonicalMap(cone(f),X)
)

-- Creates a R-ghost map, only using degrees <= n
ghost(Complex,ZZ) := (X,n) -> (
    R := ring X;
    
    -- Construct the R-approximation of X
    Q := complex R^0;
    for i from min X to n do Q = Q ++ complex(cover ker X.dd_i)[-i];
    
    -- Construct map Q -> X
    fun := i -> if (i >= min X or i <= n) then inducedMap(X_i,ker X.dd_i)*map(ker X.dd_i,Q_i,id_(Q_i)) else map(R^0,X_i);
    
    -- Return the map X -> G
    canonicalMap(cone(map(X,Q,fun)),X)
)

ghost(Complex) := (X) -> (
    ghost(X,max HH X)
)

---------------------------------------------------------------
-- This function computes the level of X with respect to G
level = method(Options => {MaxLevelAttempts => 10});

level(Complex,Complex) := ZZ => opts -> (G,X) -> (
    -- We need X to be a complex of free/projective modules, so that any map from X is zero iff it is null homotopic
    rX := resolution(X, LengthLimit => opts.MaxLevelAttempts);
    rG := resolution(G, LengthLimit => opts.MaxLevelAttempts);
    n := 0;
    f := id_(rX);
    g := f;
    homogeneous := isHomogeneous X;
    -- As long as the composition of the ghost maps g is non-zero, continue
    while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
        rX = f.target;
        f = ghost(rG,rX);
        -- minimize if possible
        if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
        
        g = f*g;
        n = n+1;
    );
    n
)
level(Complex) := ZZ => opts -> (X) -> (
    rX := resolution(X, LengthLimit => opts.MaxLevelAttempts);
    n := 0;
    f := id_(rX);
    g := f;
    h := max HH X;
    homogeneous := isHomogeneous X;
    -- As long as the composition of the ghost maps g is non-zero, continue
    while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
        rX = f.target;
        f = ghost(rX,h+n);
        -- minimize if possible
        if homogeneous then f = (minimize f.target).cache.minimizingMap * f;
        
        g = f*g;
        n = n+1;
    );
    n
)
level(Module) := ZZ => opts -> (M) -> (
    F := freeResolution(M,LengthLimit => opts.MaxLevelAttempts);
    level(F, MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Module,Module) := ZZ => opts -> (M,N) -> (
    F := freeResolution(M, LengthLimit => opts.MaxLevelAttempts);
    G := freeResolution(N, LengthLimit => opts.MaxLevelAttempts);
    level(F, G, MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Module,Complex) := ZZ => opts -> (M,N) -> (
    F := freeResolution(M, LengthLimit => opts.MaxLevelAttempts);
    level(F,N, MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Complex,Module) := ZZ => opts -> (M,N) -> (
    G := freeResolution(N, LengthLimit => opts.MaxLevelAttempts);
    level(M,G, MaxLevelAttempts => opts.MaxLevelAttempts)
)

---------------------------------------------------------------
-- Detects whether a complex is perfect
isPerfect = method( TypicalValue => Boolean );

isPerfect(Complex) := (F) -> (
    -- First make the ring and its residue field for the complex M
    R := ring F;
    m := ideal(vars R);
    k := complex(R^1/m);
    
    -- Define the one homological degree we check is zero
    d := dim(R) + max(F) + 1;
    --Compute Tor^R_d(M,k)
    G := resolution(F);
    T := tensor(G,k);
    
    -- If true, then M is perfect; otherwise, M is not perfect over R
    HH_d(T) == 0
)
--detects whether a module is perfect
isPerfect(Module) := (M) -> (
    isPerfect(complex(M))
)


--computes the support variety of a module
supportVariety = method( TypicalValue => Ideal);
supportVariety(Module) := M -> (
    R := ring M;
    k := R^1/ideal vars R;
    E := Ext(M,k);
    S := ring E;
    radical ann(E)
    )


isBuilt = method( TypicalValue => Boolean)
isBuilt(Module,Module) := (M,N) -> (
    
    R := ring M;
    R2 := ring N;
    
    if not(R === R2) then return "expected modules over the same ring";
    
    if not(isSubset(ann N, radical ann M)) then return false;
    
    k := R^1/ideal vars R;
    E1 := ExtModule(M);
    E2 := ExtModule(N);
    S := ring E1;
    T := ring E2;
    iso := map(T,S,flatten entries vars T);
    E1 = tensor(T,iso,E1);
    isSubset(ann E2, radical ann E1)
    )


--under construction

--not exported, auxiliary function to build non-proxy small modules
findgs = method(TypicalValue => Ideal)
findgs(RingElement) := Ideal => f -> (
    Q := ring f;
    R := Q/ideal(f);
    m := ideal vars R;
    ideal append({f},lift(inhomogeneousSystemOfParameters(m,R),Q)))
findgs(List) := Ideal => L -> (
    Q := ring L_0;
    R := Q/ideal(L);
    m := ideal vars R;
    ideal append(L,lift(inhomogeneousSystemOfParameters(m,R),Q)))

--not exported, auxiliary function to build non-proxy small modules
makemap = method()
makemap(Ideal,Ideal) := Matrix => (I,J) -> (
    Q := ring I;
    k := coefficientRing Q;
    m := ideal vars Q;
    A := inducedMap(J/(m*J),I/(m*I));
    matrix apply(entries A, i -> apply(i,j -> lift(j,k)))
    )

nonProxySmall = method(TypicalValue => List)
nonProxySmall(Ideal) := List => I -> (
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
    w := select(1,G, o -> (N = (Q^1/o)**(Q/I); isBuilt(M,N)));
    if w == {} then (return "none found") else w_0
    )  








-----------------------------------------------------------
-----------------------------------------------------------
-- Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

document{ 
    Key => Levels,
    Headline => "A package to compute the level with respect to the ring of a complex.",
    
    PARA {
        "This package provides a method that constructs the ghost map associated to the approximation, and using the converse ghost lemma for the ring, this gives a method to compute the level with respect to the ring. For modules the level with respect to the ring is the same as the projective dimension."},
    
    UL {
        {"J. Daniel Christensen.", EM " Ideals in triangulated categories: phantoms, ghosts and skeleta. Adv. Math., 136(2):284–339, 1998."}
    },
    
    SUBSECTION "Contributors", "The following people have generously contributed code or worked on our code at various Macaulay2 workshops.",
}

-*
document{
    Key => level,
    Headline => "compute the level with respect to the ring",
    Usage => "level F",
    Inputs => {
        {TT "F",", a complex"}
    },
    Outputs => {
        {"an integer, the level of ", TT "F"}
    }
}
*-


-- doc ///
--      Key
--        level
--        (level, Complex)
--        (level, Complex, Complex)
--        (level, Module)
--        (level, Module, Module)
--        (level, Module, Complex)
--        (level, Complex, Module)
--      Headline
--        computes the level of a complex with respect to another complex, or the ring by default
--      Usage
--        level(X)
--        level(X,G)
--        level(M)
--      Inputs
--         X:Complex
--         G:Complex -- if no G is provided, G is assumed to be the underlying ring
--         M:Module -- M is replaced with the corresponding complex
--      Outputs
--        :ZZ
--            the level of X with respect to G
--    Description
--        Example
--            R = QQ[x,y,z]
--        needsPackage("Complexes");
--             F = complex(R^0)
--            level(F)
--        Example
--            needsPackage("Complexes");
--        R = QQ[x,y]
--             M = R^1/ideal(x,y)
--            level(M)
--    Caveat
--        Text
--               Over singular rings, level only returns correct answers wrt perfect complexes
--    SeeAlso
--        ghost
-- ///

-*
       Example
           R = QQ[x,y]
       needsPackage("Complexes");
       F = complex(R^0)
       G = freeResolution(R^1/ideal(x))
       X = freeResolution(R^1/ideal(x,y^2))
       level(X,G)   
*-


-- doc ///
--      Key
--        isPerfect
--        (isPerfect, Complex)
--        (isPerfect, Module)
--      Headline
--        determines whether a complex is perfect over the ring it is defined over
--      Usage
--        isPerfect(X)
--        isPerfect(M)
--      Inputs
--         X:Complex
--         M:Module -- M is replaced with the corresponding complex
--      Outputs
--        :Boolean
--            true if the complex is perfect over the ring it is defined over and false otherwise
--    Description
--        Example
--            R = QQ[x,y]
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m);
--            isPerfect(k)
--        Example
--            R = QQ[x,y]
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m)[-2];
--            isPerfect(k)
--        Example
--            R = QQ[x,y];
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m)[2];
--            isPerfect(k)    
--        Example
--            R = ZZ/2[x,y]/ideal(x^2,y^2);
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m);
--            isPerfect(k)
--        Example
--            R = ZZ/2[x,y]/ideal(x^2,y^2);
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m)[-2];
--            isPerfect(k)
--        Example
--            R = ZZ/2[x,y]/ideal(x^2,y^2);
--        needsPackage("Complexes");
--             m = ideal(vars R);
--        k = complex(R^1/m)[2];
--            isPerfect(k)         
-- ///




document{
    Key => ghost,
    Headline => "constructs the ghost map associated to the approximation",
    Usage => "ghost F",
    Inputs => {
        {TT "F",", a chain complex"}
    },
    Outputs => {
        {"a ChainComplexMap, a ghost map starting at ", TT "F"}
    }
}

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
    assert(level(G,X) == 4)
///

end
