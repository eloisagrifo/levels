newPackage(
	"Levels",
	Version => "1.0", 
	Date => "February 20, 2020",
	Authors => {
		{Name => "Eloisa Grifo", Email => "eloisa.grifo@ucr.edu", HomePage => "http://www-personal.umich.edu/~grifo/"},
		{Name => "Janina Letz", Email => "letz@math.utah.edu", HomePage => "http://www.math.utah.edu/~letz"}
		},
	Headline => "Computing levels of complexes",
	DebuggingMode => false
	)

export {
    -- Options 
    
    -- Methods
    "Lift",
    "ghost",
--    "isNull",
    "level",
    "nonzeroc",
    "ghostnew"
    }



---------------------------------------------------------------
---------------------------------------------------------------
-- Methods
---------------------------------------------------------------
---------------------------------------------------------------





--old methods

Lift = method()
Lift(Matrix,Matrix,Matrix) := (f,g,h) -> (
	(q,r) := quotientRemainder(h*f,g);
	q
	)
Lift(ChainComplex,ChainComplex) := (F,G) -> (
	R := ring F;
	f := map(F_0,G_0,id_(R^1));
	ll := {f};
	for i from 1 to length F do (
		f = Lift(G.dd_i,F.dd_i,f);
		ll = append(ll,f)
		);
	g := (i) -> ll_i;
	map(F,G,g)
    )

--Seems to already exist
-- truncate(ChainComplex,ZZ) := (C,c) -> (
-- 	ll := {}; 
-- 	for i from c to length C do ll = append(ll,C.dd_i);
-- 	chainComplex ll
-- 	)

--This function creates the R-ghost map associated to the approximation
ghost = method();
ghost(ChainComplex) := (F) -> (
	R := ring F;
	P := R^0;
	--this is (partially) just computing a cone, for which there is a function cone()
	out := {};
	mout := {};
-- 	Complex need not start at 0
	for i from min F to max F do (
		di := (directSum(F_i,P))_[0];
		mout = append(mout,di);
		Q := cover ker F.dd_i;
		verticalmap := inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q,id_Q);
		di = di * transpose (transpose(F.dd_(i+1)) || transpose(verticalmap));
		--the dis are the differentials in cone complex  
		out = append(out,di);
		P = Q
		);
	fun := i -> if i <= max F then mout_(i - min F) else (directSum(P,F_i))_[1];
	G := chainComplex out;
	{G[-min F],map(G[-min F],F,fun)}
	)
    
    
    
isNull = method()
isNull(ChainComplexMap) := (f) -> (
	out := true;
	F := target f;
	G := source f;
	q := (directSum(F_0,G_(-1)))_[1];
	r := 0;
	i := 0;
	while out and (i<=length G) do (
		(q,r) = quotientRemainder(f_i-q*G.dd_i,F.dd_(i+1));
		if image r != 0 then out = false else i = i+1
		);
	out
	)


level = method()
level(ChainComplex) := (G) -> (
	n := 1;
	H := ghost G;
	M := H_1;
     while not isNull M do (
	  H = ghost H_0;
	  M = H_1*M;n=n+1);
     n)

	  
nonzeroc = method()     
nonzeroc := (I)-> (
    R := ring I;
    G := koszul mingens I; 
    ll := length G; 
     F := res (I,LengthLimit => ll);
     c := 0;
     f:= map(F_0,G_0,id_(R^1));
     for i from 1 to ll do(
	  f := Lift (G.dd_i,F.dd_i,f);
	  imf := image f;
	  M := image F.dd_(i+1);
	  if (imf +M)/M  !=0 then c = i);
     c)


-----------------------------------------------------------
-----------------------------------------------------------
--Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

document { 
  Key => Levels,
  Headline => "A package for computing symbolic powers of ideals",
   
   PARA {
       "This package gives the ability to compute symbolic powers, and related invariants,
       of ideals in a polynomial ring or a quotient of a polynomial ring. For example, 
       in the context of the default behavior, ", TO "symbolicPower", " assumes the 
       following definition of the symbolic power of an ideal ", TEX /// $I$, ///, 
       TEX /// $$I^{(n)} = \cap_{p \in Ass(R/I)}(I^nR_p \cap R ),$$ ///,
       "as defined by M. Hochster and C. Huneke."},

   PARA {"Alternatively, as defined in Villarreal, ", TO "symbolicPower", 
       " has the option to restrict to minimal primes versus use all associated 
       primes with ", TO "UseMinimalPrimes", ".", " In particular, the 
       symbolic power of an ideal ", TEX ///$I$ ///, " is defined as", 
       TEX /// $$I^{(n)} = \cap_{p \in Min(R/I)}(I^nR_p \cap R ),$$ ///, 
       "where ", TEX /// $Min(R/I)$///, " is the set of minimal primes in ", 
       TEX /// $I$,///},
   
   UL { 
       {"M. Hochster and C. Huneke.", EM " Comparison of symbolic and ordinary powers of ideals.", 
	   " Invent. Math. 147 (2002), no. 2, 349–369."}, 
       {"R. Villarreal.", EM " Monomial algebras.", " Second edition. Monographs and Research Notes 
	   in Mathematics. CRC Press, Boca Raton, FL, 2015. xviii+686 pp. ISBN: 978-1-4822-3469-5."}, 
       {"Hailong Dao, Alessandro De Stefani, Eloísa Grifo, Craig Huneke, and Luis Núñez-Betancourt. ", 
	   EM "Symbolic powers of ideals.", "in Singularities and foliations. Geometry, topology and applications, pp. 387-432, Springer Proc. Math. Stat., 222, Springer, Cham, 2018. See ", HREF("https://arxiv.org/abs/1708.03010","https://arxiv.org/abs/1708.03010"), "."} 
       },
  
   SUBSECTION "Contributors", "The following people have generously
   contributed code or worked on our code at various Macaulay2
   workshops.",
     
     UL {
	 "Ben Drabkin",
	 "Andrew Conner",
	 "Alexandra Seceleanu",
	 "Branden Stone",
	 "Xuehua (Diana) Zhong"
	},

   SUBSECTION "A Quick Introduction",
   UL {
    TO "Computing symbolic powers of an ideal",
    TO "Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"
    },
    
 
  SUBSECTION "Other Related Examples",
  UL {
    TO "The Containment Problem",
    TO "Sullivant's algorithm for primes in a polynomial ring",
    TO "The Packing Problem"    
  }

}  






-- tests

TEST ///
   S = QQ[x,y,z];
   I = ideal(x,y,z);
   assert(isSymbPowerContainedinPower(I,2,2) == true)
///

--bigHeight
TEST ///
R=ZZ/2[x,y,z]
I=ideal(x,y)
assert(bigHeight(I)==2)
///

TEST ///
R=QQ[x,y,z]
I=ideal(x,y^3,z^2)
assert(bigHeight I==3)
///


TEST ///
R=QQ[x,y,z]
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3))
assert(bigHeight(I)==2)
///


--symbolicPower
TEST ///
R=QQ[x,y,z]
I=ideal(y-z,x+z)
assert(symbolicPower(I,2)==ideal(y^2-2*y*z+z^2,x*y-x*z+y*z-z^2,x^2+2*x*z+z^2))
///

TEST ///
R=QQ[x,y,z]
I=ideal(x)
assert(symbolicPower(I,2)==ideal(x^2))
///

TEST ///
R=QQ[x,y,z]
I=ideal(x+1)
assert(symbolicPower(I,2)==ideal(x^2+2*x+1))
///


end
