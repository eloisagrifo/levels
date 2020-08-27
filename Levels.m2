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
    "level"
}

needsPackage "Complexes"

---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

-- This function creates the R-ghost map associated to the approximation
ghost = method();
ghost(Complex) := (F) -> (
	R := ring F;
	
	-- Construct the R-approximation of F
	Q := complex R^0;
	for i from min F to max F do Q = Q ++ complex(cover ker F.dd_i)[-i];
	
	-- Construct map Q -> F
	fun := i -> if (i >= min F or i <= max F) then inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q_i,id_(Q_i)) else map(R^0,F_i);
	
	-- Take the cone, and make it minimal
	G := cone(map(F,Q,fun));
	
	-- Return the map F -> G
	canonicalMap(G,F)
)
ghost(Module) := M -> (
	ghost(complex M)
)

-- This function computes the level of G with respect to R
level = method(TypicalValue => ZZ, Options => {MaxLevelAttempts => 100})
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
level(Module) := ZZ => opts -> (M) -> (
	level(complex(M), MaxLevelAttempts => opts.MaxLevelAttempts)
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
    	loadPackage "Complexes"
	R = QQ[x,y,z]
	F = freeResolution (R^2)
	assert(level F == 1)
///

TEST ///
	R = QQ[x,y,z]/ideal(x*y*z)
	loadPackage "Complexes"
	G = freeResolution (R^2)
	F = G ++ G[1] ++ G[-1]
	assert(level F == 1)
///

TEST ///
	R = QQ[x,y,z]
	loadPackage "Complexes"
	I = ideal vars R
	F = freeResolution(R^1/I)
	assert(level F == 4)
///

TEST ///
	R = QQ[x,y,z]
	loadPackage "Complexes"
	I = ideal vars R
	F = freeResolution(R^1/I)[-3]
	assert(level F == 4)
///

TEST ///
	R = QQ[x,y,z]
	loadPackage "Complexes"
	I = ideal vars R
	F = freeResolution(R^1/I^2)
	assert(level F == 4)
///

end
