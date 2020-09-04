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
    "isPerfect"
}

needsPackage "Complexes"

---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-- This function creates the R-ghost map associated to the approximation
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

---------------------------------------------------------------
-- This function computes the level of X with respect to G
level = method(TypicalValue => ZZ, Options => {MaxLevelAttempts => 100})

level(Complex,Complex) := ZZ => opts -> (G,X) -> (
	-- We need X to be a complex of free/projective modules, so that any map from X is zero iff it is null homotopic
	rX := resolution X;
	rG := resolution G;	
	n := 0;
	f := id_(rX);
	g := f;
	-- As long as the composition of the ghost maps g is non-zero, continue
	while ((not isNullHomotopic g) and (n < opts.MaxLevelAttempts)) do (
		f = ghost(rG,f.target);
		f = (minimize f.target).cache.minimizingMap * f;
		g = f*g;
		n = n+1;
		print "+1";
	);
	n
)
level(Complex) := ZZ => opts -> (X) -> (
	level(complex((ring X)^1),X, MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Module) := ZZ => opts -> (M) -> (
	level(complex(M), MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Module,Module) := ZZ => opts -> (M,N) -> (
	level(complex(M),complex(N), MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Module,Complex) := ZZ => opts -> (M,N) -> (
	level(complex(M),N, MaxLevelAttempts => opts.MaxLevelAttempts)
)
level(Complex,Module) := ZZ => opts -> (M,N) -> (
	level(M,complex(N), MaxLevelAttempts => opts.MaxLevelAttempts)
)

---------------------------------------------------------------
-- Detects whether a complex is perfect
isPerfect = method();

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
       level(X,G)
       level(M)
     Inputs
        X:Complex
    	G:Complex -- if no G is provided, G is assumed to be the underlying ring
        M:Module -- M is replaced with the corresponding complex
     Outputs
       :ZZ
           the level of X with respect to G
   Description
       Example
           R = QQ[x,y,z]
	   needsPackage("Complexes");
     	   F = complex(R^0)
    	   level(F)
       Example
           R = QQ[x,y]
     	   M = R^1/ideal(x,y)
    	   level(M)
   Caveat
       Text
       	   Over singular rings, level only returns correct answers wrt perfect complexes
   SeeAlso
       ghost
///

-*
       Example
           R = QQ[x,y]
	   needsPackage("Complexes");
	   F = complex(R^0)
	   G = freeResolution(R^1/ideal(x))
	   X = freeResolution(R^1/ideal(x,y^2))
	   level(X,G)   
*-


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
