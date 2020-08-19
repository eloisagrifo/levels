newPackage(
	"Levels",
	Version => "1.0", 
	Date => "July 30, 2020",
	Authors => {
		{Name => "Eloisa Grifo", Email => "eloisa.grifo@ucr.edu", HomePage => "http://www-personal.umich.edu/~grifo/"},
		{Name => "Janina C. Letz", Email => "jletz@math.uni-bielefeld.de", HomePage => "http://www.math.uni-bielefeld.de/~jletz"}
	},
	Headline => "Computing levels of complexes",
	DebuggingMode => false
)

export {
    -- Options 
    
    -- Methods
    "ghost",
   "isNull",
    "level"
}

needsPackage "Complexes"

---------------------------------------------------------------
-- TODO
---------------------------------------------------------------
-- Use minimize to be more efficient


---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------

-- This function creates the R-ghost map associated to the approximation
ghost = method();
ghost(Complex) := (F) -> (
-- 	F = resolution F; -- Need to take this, since we later will check if the map is homotopically zero, maybe change it there?
	R := ring F;
	P := R^0;
	out := {};
	mout := {};
	
	-- Construct the cone of the approximation
	for i from min F to max F do (
		-- Approximation
		Q := cover ker F.dd_i; -- Free module mapping surjective onto H_i(F)
		mapprox := inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q,id_Q); -- map from Q to F_i
		
		-- Cone G of the approximation (differentials are saved in out), with map F->G (saved in mout)
		mi := (directSum(F_i,P))_[0];
		mout = append(mout,mi);
		d := mi * (F.dd_(i+1) | mapprox); -- differential d_{i+1} of the cone
		out = append(out,d);
		P = Q;
	);
	
	-- Create the cone from out and the map from mout
	G := complex out;
	fun := i -> if i <= max F then mout_(i - min F) else (directSum(P,F_i))_[1];
	map(G[-min F],F,fun) -- Shift the cone C to line up with F (the lists out, mout ignore the degrees)
)


-- This functions checks whether a chain map is null-homotopic
isNull = method()
isNull(ComplexMap) := (f) -> (
	out := true;
	F := target f;
	G := source f;
	i := min G;
	q := (directSum(F_i,G_(i-1)))_[1]; -- Homotopy in degree i-1
	r := 0;
	while out and (i<=max G) do (
		(q,r) = quotientRemainder(f_i-q*G.dd_i,F.dd_(i+1));
		if image r != 0 then out = false else i = i+1;
	);
	out
)


level = method()
level(Complex) := (G) -> (
	-- TODO: First check that G is non-zero (if it is zero, return 0)
	-- TODO: Replace G by its free resolution (is that necessary? it seems really hard to create complexes not consisting of free modules)
	n := 1;
	f := ghost G;
	g := f;
	-- TODO: Make sure the target for isNull is a complex of free modules
	-- As long as the composition of the ghost maps g is non-zero, continue
	-- TODO: This is an infinite loop, add exit condition
	while not isNull g do (
		f = ghost f.target;
-- 		The problem is here, f*g is not possible, I don't know why
		g = f*g;
		n=n+1
	);
	n
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
	
	UL {
		{}
	},
}

document{
	Key => level,
	Headline => "compute the level with respect to the ring",
	Usage => "level F",
	Inputs => {
		{TT "F",", a chain complex"}
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
	F = resolution R^2
	assert(level F == 1)
///

TEST ///
	R = QQ[x,y,z]/ideal(x*y*z)
	G = resolution R^2
	F = G ++ G[1] ++ G[-1]
	assert(level F == 1
///

TEST ///
	R = QQ[x,y,z]
	I = ideal vars R
	F = koszul mingens I
	assert(level F == 4)
///

TEST ///
	R = QQ[x,y,z]
	I = ideal vars R
	F = (koszul mingens I)[-3]
	assert(level F == 4)
///

TEST ///
	R = QQ[x,y,z]
	I = ideal vars R
	F = koszul mingens (I^2)
	assert(level F == 4)
///

end
