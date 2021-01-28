-- Installing the Package
uninstallPackage "Levels"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "Levels"
check "Levels"
loadPackage "Complexes"

---------------------------------------------------------------
-- Tests for level wrt R^1
R = QQ[x,y,z]

F = complex R^0
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 0

F = complex R^2
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 1

R = QQ[x,y,z]/ideal(x*y*z)
G = complex R^2
F = G ++ G[1] ++ G[-1]
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 1

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I)[-3]
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x,y,z]
I = ideal vars R
F = freeResolution(R^1/I^2)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 4

R = QQ[x]
I = ideal vars R
F = complex(R^1/I)
time level F
time level(R^1,F)
time level(F,Strategy => "coghost")
-- Correct answer: 2

---------------------------------------------------------------
-- Tests for ghost with respect to a perfect complex
R = QQ[x,y]
G = freeResolution(R^1/ideal(x), LengthLimit => 10)
X = freeResolution(R^1/ideal(x,y^2))
time level(G,X)
time level(G,X,Strategy => "coghost")
-- Correct answer: 2

R = QQ[x_1 .. x_6]
M = complex(R^1/minors(2,matrix{{x_1, x_2, x_3},{x_4, x_5, x_6}}))
N = complex(R^1/ideal(x_1,x_2,x_3))
time level(N,M)

R = QQ[x]
N = complex(R^1/ideal(x^3))
M = complex(R^1/ideal(x^7))
time level(N,M)

R = QQ[x,y]
M = complex(R^1/ideal(x^2,y^2))
N = complex(R^1/ideal(x,y))
time level(M,N)


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

-- Error for level
-- Level
R = ZZ[x,a]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x*a,a^2}})
f2 = map(source f1,,matrix{{x*a},{-x^2}})
F = complex{f1,f2}
isWellDefined F
level(F,MaxLevelAttempts => 4)
-- Level should be <= 3

R = ZZ[x]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x,1}})
f2 = map(source f1,,matrix{{x},{-x^2}})
F = complex{f1,f2}
isWellDefined F
level(F,MaxLevelAttempts => 4)
-- This makes no sense, since F is not exact (or equivalently id_F is not nullhomotopic)
isExact F
isNullHomotopic id_F

-- Problem is that resolution does not work as it should:
R = ZZ[x]
S = R/ideal(promote(2,R))
f1 = map(S^1,S^2,matrix{{x,1}})
f2 = map(source f1,,matrix{{x},{-x^2}})
F = complex{f1,f2}
isQuasiIsomorphism(resolutionMap F)
-- It probably does not work since F is not homogeneous


?level

ann M


--Testing support varieties
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
R = QQ[x]/ideal(x^2)
M = R^1/ideal(x)
time isBuilt(M,R^1)


R = QQ[x,y,z]/ideal"x2,y2,z2"
k = R^1/ideal(x,y,z)
M = R^1/ideal"x,y"
time isBuilt(k,R^1)
time isBuilt(R^1,k)
time isBuilt(M,R^1)
time isBuilt(R^1,M)

supportVariety(M)
N = R^1/ideal(x,y^2,z^2)
time isBuilt(N,R^1)
time isBuilt(R^1,N)

E1 = extKoszul(M)
E2 = extKoszul(R^1)
S = ring E1
T = ring E2
M


--testing isBuilt
R = QQ[x,y,z]/ideal"x2,yz"
M = R^1/ideal(x,y)
time isBuilt(M,R^1)
time isBuilt(R^1,M)
time level(R^1,M) -- returns 5 but should be infinity!
time level(M,R^1, MaxLevelAttempts => 20)
supportVariety(M)
N = R^1/ideal(x,y^2,z^2)
time isBuilt(N,R^1)
time isBuilt(R^1,N)



--changing freeResolution options
uninstallPackage "Complexes"
restart
installPackage "Complexes"
viewHelp freeResolution

R = QQ[x,y,z]/ideal"x2,yz"
M = R^1/ideal(x,y)
freeResolution(M, LengthLimit => 10)


--testing nonProxySmall
uninstallPackage "Levels"
restart
path = append(path,"~/Documents/GitHub/levels");
installPackage "Levels"
Q = QQ[x,y,z]
I = ideal(x^2-y^2, x^2-z^2, x*y, y*z, x*z)
time nonProxySmall I

-- Compare different methods for level wrt R^1
uninstallPackage "Levels"
restart
loadPackage "Complexes"
installPackage "Levels"

R = QQ[x,y,z]
X = R^1/ideal(x^2,y^2,z^2)
f1 = map(R^1,R^2,matrix{{x,y^2}})
f2 = map(source f1,X,matrix{{x},{1}})
F = complex{f1,f2}

R = QQ[x]/ideal(x^2)
X = complex(R^4/ideal(x))
time level(X,MaxLevelAttempts => 5)
time level(R^1,X,MaxLevelAttempts => 5)
Y = complex(R^1) ++ X[2]
time level(Y,MaxLevelAttempts => 10)
time level(complex R^1,Y,MaxLevelAttempts => 10)

-- Some example
R = QQ[x,y]
needsPackage("Complexes");
F = complex(R^0)
G = freeResolution(R^1/ideal(x))
X = freeResolution(R^1/ideal(x,y^2))
level(G,X)  

-- Truncations of the resolution and how they affect the result of level
R = QQ[x]/ideal(x^2)
X = complex(R^1/ideal(x))
resolution(X,LengthLimit => 5)
resolution(X[3],LengthLimit => 5) == resolution(X[3]++X[-3],LengthLimit => 5)
-- Examples that explore this weakness
R = QQ[x,y]
X = complex(R^1/ideal(x,y))
level(X,X++X[-2],MaxLevelAttempts => 3)
-- This should be 1, but returns 3
level(X,X++X[-4],MaxLevelAttempts => 6)



uninstallPackage "Levels"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "Levels"
Q = QQ[x,y]
I = ideal"xy,x2"
nonProxySmall(I)
R = Q/I
nonProxySmall(R)
M1 = R^1/ideal"y"
M2 = R^1/ideal"x+y"
M3 = R^1/ideal"x"
isBuilt(R^1,M1)
isBuilt(R^1,M2)
isBuilt(R^1,M3)
isBuilt(R^1,R^1/ideal"x,y")
k = R^1/ideal(x,y)
isBuilt(k,R^1)
d = depth R + 3
time level(R^1,k,MaxLevelAttempts => d, LengthLimit => d)

-- Installing the Package
uninstallPackage "ThickSubcategories"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "ThickSubcategories"
check "ThickSubcategories"
needsPackage "Complexes"

-----------------------------------------------------------
-- Test if it makes sense to cut off the lower degree at the end of the while loop

R = QQ[x,y]
X = freeResolution coker vars R
time level X
-- 0.220509
-- 0.183668

R = QQ[x,y]/ideal(x^2)
X = freeResolution(R^1/ideal(y^2))
time level X
-- 0.133126
-- 0.127081

R = QQ[x,y,z]/ideal(x*y,y*z,z*x,x+y+z)
X = freeResolution(coker vars R,LengthLimit => 3)
time level X
-- 1.73377
-- 0.949323

R = QQ[x,y,z]/ideal(x*y,y*z,z*x,x+y+z)
X = freeResolution(coker vars R,LengthLimit => 4)
time level X
-- 21.9887
-- 6.78384


----------------------------------------------------------------------------
-- Test for restriction of scalars

uninstallPackage "ThickSubcategories"
restart
installPackage "ThickSubcategories"
needsPackage "Complexes"

-- Test Module Map
R = QQ[x,y,z]/ideal(x^3,x*y)
M = R^1/ideal(y)
N = R^1/ideal(x,y)
f = inducedMap(N,M)

restrict f

-- Test Complex
R = QQ[x,y,z]/ideal(x^3,x*y)
M = R^1/ideal(y)
F = complex(M,Base => 3)

restrict F

F = freeResolution(M,LengthLimit => 2)

G = restrict F



-- Installing the Package
uninstallPackage "ThickSubcategories"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "ThickSubcategories"
--check "ThickSubcategories"
needsPackage "Complexes"
R = QQ[x]
M = complex(R^1/ideal"x2")
extKoszul(M,M)
N=M


needsPackage"CompleteIntersectionResolutions"
makeHomotopies(f,C)


--extKoszul = method();
--extKoszul(Complex,Complex) := Module => (M,N) -> (
    B = ring M;
--    if B != ring(N) then error "need modules over the same ring";
    if not isCommutative B
    then error "'Ext' not implemented yet for noncommutative rings.";
    if not isHomogeneous B
    then error "'Ext' received modules over an inhomogeneous ring";
    if ((not isHomogeneous M) or (not isHomogeneous N))
    then error "received an inhomogeneous module";
    
    --this needs to be fixed later -- answer over the wrong ring
    if M == 0 then return B^0;
    if N == 0 then return B^0;
    
    p = presentation B;
    A = ring p;
    I = ideal mingens ideal p;
    n = numgens A;
    c = numgens I;
    f = apply(c, i -> I_i);
    
    M' = restrict(M,A);
    assert isHomogeneous M'; -- is this necessary, that is is there a way that the construction could give a non-homogeneous module?
    
--    N := coker(vars B);
--    pN := lift(presentation N,A);
--    N' := cokernel ( pN | p ** id_(target pN) );
    
    C := resolution M';
    
    -- Construct ring of cohomological operators
    K := coefficientRing A;
    X := getSymbol "X"
    S := K[ X_1 .. X_c, toSequence gens A,
           Degrees => { apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
                        apply(0 .. n-1, j -> prepend( 0,   degree A_j))},
           Heft => {-2,1} ]
    
    -- make a monoid whose monomials can be used as indices
    Rmon = monoid [X_1 .. X_c,Degrees=>{c:{2}}]
    -- make group ring, so 'basis' can enumerate the monomials
    R = K Rmon
    
    -- make a hash table to store the blocks of the matrix
    blks := new MutableHashTable
    blks#(exponents 1_Rmon) = C.dd
    scan(0 .. c-1, i -> blks#(exponents Rmon_i) = nullHomotopy (- f_i*id_C))
    
    -- Warning: This is a recursive function.
    -- a helper function to list the factorizations of a monomial
    -- Input: gamma is the list of exponents for a monomial
    -- Return a list of pairs of lists of exponents showing the possible factorizations of gamma.
    factorizations := (gamma) -> (
        if (gamma === {}) then (
            { ({}, {}) }
        ) else (
            i := gamma#-1;
            splice apply( factorizations drop(gamma,-1), 
                          (alpha,beta) -> apply (0..i, 
                                                 j -> (append(alpha,j), append(beta,i-j))
                                                )
                        )
        )
    )
    
    scan( 4 .. length C + 1, 
          d -> if even d then (
            scan( flatten \ exponents \ leadMonomial \ first entries basis(d,R), 
             gamma -> (
               s := - sum(factorizations gamma,
                 (alpha,beta) -> (
                   if blks#?alpha and blks#?beta
                   then blks#alpha * blks#beta
                   else 0));
               -- compute and save the nonzero nullhomotopies
               if s != 0 then blks#gamma = nullHomotopy s;
               ))
          )
        )
    
    -- make a free module whose basis elements have the right degrees
    spots = C -> sort select(keys C, i -> class i === ZZ)
    Cstar = S^(apply(spots C,i -> toSequence apply(degrees C_i, d -> prepend(i,d))))
    
    -- assemble the matrix from its blocks.
    -- We omit the sign (-1)^(n+1) which would ordinarily be used,
    -- which does not affect the homology.
    toS = map(S,A,apply(toList(c .. c+n-1), i -> S_i),DegreeMap => prepend_0)
    Delta = map( Cstar,
                  Cstar, 
                  transpose sum(keys blks, m -> S_m * toS sum blks#m),
                  Degree => { -1, degreeLength A:0 })
    DeltaBar = Delta ** (toS ** M')
    if debugLevel > 10 then (
        assert isHomogeneous DeltaBar;
        assert(DeltaBar * DeltaBar == 0);
        stderr << describe ring DeltaBar <<endl;
        stderr << toExternalString DeltaBar << endl;
    );
    
    -- now compute the total Ext as a single homology module
    tot := minimalPresentation homology(DeltaBar,DeltaBar);
    tot
)



--new idea
extKoszul = method();
extKoszul(Complex,Complex) := Module => (M,N) -> (
    B := ring M;
--    if B != ring(N) then error "need modules over the same ring";
    if not isCommutative B
    then error "'Ext' not implemented yet for noncommutative rings.";
    if not isHomogeneous B
    then error "'Ext' received modules over an inhomogeneous ring";
    if ((not isHomogeneous M) or (not isHomogeneous N))
    then error "received an inhomogeneous module";
    
    --this needs to be fixed later -- answer over the wrong ring
    if M == 0 then return B^0;
    if N == 0 then return B^0;
    
    p := presentation B;
    A := ring p;
    I := ideal mingens ideal p;
    n := numgens A;
    c := numgens I;
    f := apply(c, i -> I_i);
    
    M' := restrict(M,A);
    assert isHomogeneous M'; -- is this necessary, that is is there a way that the construction could give a non-homogeneous module?
    
--    N := coker(vars B);
--    pN := lift(presentation N,A);
--    N' := cokernel ( pN | p ** id_(target pN) );
    
    C := resolution M';
    
    -- Construct ring of cohomological operators
    K := coefficientRing A;
    X := getSymbol "X";
    S := K[ X_1 .. X_c, toSequence gens A,
           Degrees => { apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
                        apply(0 .. n-1, j -> prepend( 0,   degree A_j))},
           Heft => {-2,1} ];
    
    -- make a monoid whose monomials can be used as indices
    Rmon := monoid [X_1 .. X_c,Degrees=>{c:{2}}];
    -- make group ring, so 'basis' can enumerate the monomials
    R := K Rmon;
    X := chainComplex(C);
    homotopies := makeHomotopies(f,X);
    spots := C -> sort select(keys C, i -> class i === ZZ);
    Cstar := S^(apply(spots X,i -> toSequence apply(degrees X_i, d -> prepend(i,d))));
    
    -- assemble the matrix from its blocks.
    -- We omit the sign (-1)^(n+1) which would ordinarily be used,
    -- which does not affect the homology.
    toS := map(S,A,apply(toList(c .. c+n-1), i -> S_i),DegreeMap => prepend_0);
    Delta := map( Cstar,
                  Cstar, 
                  transpose sum(keys homotopies, m -> S_m * toS sum homotopies#m),
                  Degree => { -1, degreeLength A:0 });
    DeltaBar := Delta ** (toS ** M');
    if debugLevel > 10 then (
        assert isHomogeneous DeltaBar;
        assert(DeltaBar * DeltaBar == 0);
        stderr << describe ring DeltaBar <<endl;
        stderr << toExternalString DeltaBar << endl;
    );
    
    -- now compute the total Ext as a single homology module
    tot := minimalPresentation homology(DeltaBar,DeltaBar);
    tot
)
    

---testing extKoszul jan 28
needsPackage "CompleteIntersectionResolutions"
uninstallPackage "ThickSubcategories"
uninstallPackage "Complexes"
restart
path=append(path,"~/Documents/Github/levels");
installPackage "Complexes"
installPackage "ThickSubcategories"
loadPackage "ThickSubcategories"
needsPackage "Complexes"
k = QQ
R = k[x]/(x^2)
M = complex(R^1/(x))
extKoszul(complex(M),complex(M))
--extKoszul = method();
--extKoszul(Complex,Complex) := Module => (M,N) -> (
    B = ring M;
--    if B != ring(N) then error "need modules over the same ring";
    if not isCommutative B
    then error "'Ext' not implemented yet for noncommutative rings.";
    if not isHomogeneous B
    then error "'Ext' received modules over an inhomogeneous ring";
    if ((not isHomogeneous M) or (not isHomogeneous N))
    then error "received an inhomogeneous module";
    
    --this needs to be fixed later -- answer over the wrong ring
    if M == 0 then return B^0;
    if N == 0 then return B^0;
    
    p = presentation B;
    A = ring p;
    I = ideal mingens ideal p;
    n = numgens A;
    c = numgens I;
    f = apply(c, i -> I_i);
    
    M' = restrict(M,A);
    assert isHomogeneous M'; -- is this necessary, that is is there a way that the construction could give a non-homogeneous module?
    
--    N := coker(vars B);
--    pN := lift(presentation N,A);
--    N' := cokernel ( pN | p ** id_(target pN) );
    
    C = resolution(M');
    
    -- Construct ring of cohomological operators
    K = coefficientRing A;
    X = getSymbol "X";
    S = K[ X_1 .. X_c, toSequence gens A,
           Degrees => { apply(0 .. c-1, i -> prepend(-2, - degree f_i)),
                        apply(0 .. n-1, j -> prepend( 0,   degree A_j))},
           Heft => {-2,1} ];
    
    -- make a monoid whose monomials can be used as indices
    Rmon = monoid [X_1 .. X_c,Degrees=>{c:{2}}];
    -- make group ring, so 'basis' can enumerate the monomials
    R = K Rmon;
    
    C = chainComplex(C);
    homotopies = makeHomotopies(matrix{f},C);
    -- Problem: All of this happens over the wrong ring, should be over R, but happens over A (they are isomorphic). Is this a problem? Might conflict later with S.
    -- The entries of the hash table are indexed by {J,i} (different than before)
    
    -- keys does different things for Complex and ChainComplex. This is just about getting all the degrees where C is defined.
    spots = C -> sort select(keys C, i -> class i === ZZ);
    Cstar = S^(apply(spots C,i -> toSequence apply(degrees C_i, d -> prepend(i,d))));
    
    -- assemble the matrix from its blocks.
    -- We omit the sign (-1)^(n+1) which would ordinarily be used,
    -- which does not affect the homology.
    toS = map(S,A,apply(toList(c .. c+n-1), i -> S_i),DegreeMap => prepend_0);
    
    forDelta = apply(apply(keys homotopies, first), 
	m -> product(apply(m, i -> S_i))); 
    --each entry of forDelta (in order) and multiply by
    -- whatever the correct substitute for
    --toS sum  homotopies#m
    
    Delta = map( Cstar,
                  Cstar, 
                  transpose sum(keys homotopies), m -> S_(m_0) * toS sum  homotopies#m),
                  Degree => { -1, degreeLength A:0 });
    DeltaBar = Delta ** (toS ** M');
    if debugLevel > 10 then (
        assert isHomogeneous DeltaBar;
        assert(DeltaBar * DeltaBar == 0);
        stderr << describe ring DeltaBar <<endl;
        stderr << toExternalString DeltaBar << endl;
    );
    
    -- now compute the total Ext as a single homology module
    tot = minimalPresentation homology(DeltaBar,DeltaBar);
    tot
)
