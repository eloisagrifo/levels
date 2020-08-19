R = QQ[x,y,z]
I = ideal vars R
G = koszul mingens (I^2)
level G

R = QQ[x,y]
I = ideal vars R 
G = koszul mingens (I)
level G


uninstallPackage "Levels"
restart
path = append(path,"~/Dropbox/LevelsM2");
installPackage "Levels"

R = QQ[x,y,z]
F = chainComplex{matrix{{x,y}},matrix{{x*y},{-x^2}}}
ghost(F[-1]) 
ghost(F)

F = F[1]

	R = ring F
	P = R^0
	--this is (partially) just computing a cone, for which there is a function cone()
	out = {}
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
	fun := i -> if i <= length F then mout_(i+ min F) else (directSum(P,F_i))_[1];
	G := chainComplex out;
	{G,map(G[-min F],F,fun)}
	)
    
    
    
    


G = chainComplex{matrix{{z,y,0},{x,0,1}}}



--Issues with operations on complexes:
restart
C = resolution cokernel matrix {{4,5}}
C[-2]
C ++ C[-2]
code methods ++
restart
R = QQ[x,y,z]
F = new ChainComplex
F#0 = R^1
F#1 = 0
G = new ChainComplex
G#0 = 0
G#1 = R^1
F ++ G
F
G.dd_0


chainComplex()

F.dd

H = res I
L = res ideal(x)
H ++ L
f = inducedMap(R^1/I,R^1/ideal(x))
f = inducedMap(H,L)

H.dd_4



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
	fun := i -> if i <= length F then mout_i else (directSum(P,F_i))_[1];
	G := chainComplex out;
	{G,map(G,F,fun)}
	)
    
    
    
    


cone(H,L)

newcone = method()
newcone(ChainComplexMap) := ChainComplex => f -> (
    C := source f;
    D := target f;
    mC := min C;
    mD := min D;
    m := min({mC,mD});
    MC := max C;
    MD := max D;
    M := max({MC,MD})+1;
    (for (m <= i <= (mC-1)) do C#i = 0);
    (for (m <= i <= (mD-1)) do D#i = 0);

    
ChainComplex
code methods cone

toList(2 .. 1)

F = chainComplex({map(0,R^1,{}),map(R^1,0,{})})
?map
map(0,R^1,{})

---sample method
symbPowerMon = method(TypicalValue => Ideal)
symbPowerMon(Ideal,ZZ) := Ideal => (I,n) -> (
    if isSquareFree I 
    then (
	assP := associatedPrimes(I); 
	intersect apply(assP, i -> fastPower(i,n))
	)
    else (
	--If I is simply monomial, one can collect the primary components in a decomposition
	--of I and intersect the powers of the *maximal* ones
	Pd:=primaryDecomposition I;
    	P:=apply(Pd, a-> radical a);
    	maxP:={};
    	apply(P, a-> if #select(P, b-> isSubset(a,b))==1 then maxP=maxP|{a});
    	Q:=for p in maxP list (intersect select(Pd, a-> isSubset(a,p)));
    	intersect apply(Q,i -> fastPower(i,n))
	)
    )



---Sample documentation



doc ///
     Key
     	  "A quick introduction to this package"
     Headline
     	  How to use this package
     Description
     	  Text
	       Here is a list of some examples which illustrate various parts of this package.
	       
	       {\bf First examples which show how to use this package}
    	       
	       $\bullet$ @TO"Computing symbolic powers of an ideal"@
	       
	       $\bullet$ @TO"Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"@
 
               {\bf Other examples which illustrate this package}

               $\bullet$ @TO"The Containment Problem"@
	       
	       $\bullet$ @TO"Sullivant's algorithm for primes in a polynomial ring"@
    	       	     
	       {\bf The Packing Problem}
	       
	       $\bullet$ @TO"The Packing Problem"@
	       
 	  	  
///



doc ///
   Key
       bigHeight
       (bigHeight, Ideal)
   Headline
       computes the big height of an ideal
   Usage
       bigHeight(I)
   Inputs
        I:Ideal
   Outputs
       :ZZ
           the largest height of an associated prime of I
   Description
       Text  
       	   level bla bla 

       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   bigHeight(J)
   SeeAlso
       codim
       assPrimesHeight
   Caveat
       bigHeight works faster than assPrimesHeight
///


doc ///
   Key
       assPrimesHeight
       (assPrimesHeight, Ideal)
   Headline
       The heights of all associated primes
   Usage
       assPrimesHeight(I)
   Inputs
        I:Ideal
   Outputs
       :List
           the heights of all associated primes of I
   Description
       Text  
           The algorithm is based on the following result by Eisenbud-Huneke-Vasconcelos, 
	   in their 1993 Inventiones Mathematicae paper:
	   
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all $d$
	   
	   $\bullet$ If $P$ is an associated prime of $M$ of codimension $d :=$ codim $P > $ codim $M$, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in $P$
	   
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension $d$.	   

       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   assPrimesHeight(J)
   SeeAlso
       bigHeight
       codim
   Caveat
       bigHeight works faster than using assPrimesHeight and then taking the maximum
///




doc ///
     Key 
         squarefreeInCodim
	 (squarefreeInCodim,Ideal)
     Headline 
         finds square-fee monomials in ideal raised to the power of the codimension.
     Usage 
         squarefreeInCodim(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal $I$, returns all square-free monomials in a minimal generating set of $I^c$ where $c$ is the codimension of $I$.

       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   squarefreeInCodim(I) 
     SeeAlso 
	  squarefreeGens
///

