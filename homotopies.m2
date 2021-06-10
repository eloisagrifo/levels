needsPackage "Complexes"
needsPackage "CompleteIntersectionResolutions"

makeHomotopies(Matrix, Complex, ZZ) := (f,F,d) ->(
                 --given a 1 x lenf matrix f and a chain complex 
                 -- F_min <-...,
                 --the script attempts to make a family of higher homotopies
                 --on F for the elements of f.
                 --The output is a hash table {{J,i}=>s), where     
                 --J is a list of non-negative integers, of length = ncols f
                 --and s is a map F_i->F_(i+2|J|-1) satisfying the conditions
                 --s_0 = differential of F
                 -- s_0s_{i}+s_{i}s_0 = f_i
                 -- and, for each index list I with |I|<=d,
                 -- sum s_J s_K = 0, when the sum is over all J+K = I
                 S := ring f;
                 if source f == 0 then return hashTable{};
                 if numrows f != 1 then error"expected a 1 x ? matrix";
                 flist := flatten entries f;
                 lenf := #flist;
                 degs := apply(flist, fi -> degree fi); -- list of degrees (each is a list)
                 

                 minF := min F;
                 maxF := max F;
                 if d>max F then d=maxF;

                 e0 := (expo(lenf,0))_0;

                 e1 := expo(lenf,1);
                 
                 H := new MutableHashTable;
                 
                 --make the 0  homotopies into F_minF;
                 for i from minF to d+1 do H#{e0,i} = F.dd_i;
                 scan(#flist, j-> H#{e1_j,minF-1} = map(F_minF, F_(minF-1), 0));

                 --the rest of the first homotopies
                 for i from minF to d do
                           scan(#flist,
                           j-> H#{e1_j,i} = (-H#{e1_j,i-1}*H#{e0,i}+flist_j*id_(F_i))//H#{e0,i+1}
                           );
                       
                 --the higher homotopies
                 for k from 2 to d do(
                      e := expo(lenf,k);
                      apply(e, L ->(
                        k := sum L;
                        H#{L,minF-1}= map(F_(minF+2*k-2),F_(minF-1),0);
                        for i from minF to d-2*k+1 do
                          H#{L,i} = -sum(expo(lenf,L), 
                             M->(H#{L-M,i+2*sum(M)-1}*H#{M,i}))//H#{e0,i+2*k-1};
                        )));

                 --correct the degrees, and return a HashTable
                 H1 := hashTable apply(keys H, k->
                 {k, map(F_(k_1+2*sum (k_0)-1), 
                         tensorWithComponents( S^{-sum(#k_0,i->(k_0)_i*degs_i)},F_(k_1)), 
                                                     H#k)});
                 H1)




R = QQ[x,y,z]
f = {x*y,y*z}
F = freeResolution(R^1/ideal vars R)
d = 5

makeHomotopies(List, Complex, ZZ) := (f,F,d) ->(
    S = ring F;
    if f == {} then return hashTable{};
    lengthf = #f;
    degs = apply(f, i -> degree i); -- list of degrees (each is a list)
    minF := min F;
    maxF := max F;
    if d>max F then d=maxF;
    e0 = (expo(lengthf,0))_0;
    L0 = apply(toList((minF+1) .. d), i -> ({e0,i},F.dd_i))
    H = new MutableHashTable from L0
    e1 = expo(lengthf,1)
    p1 = flatten table(toList(minF .. (d-1)), toList(0 .. (lengthf-1)), (i,j) -> (i,j))
    scan(p1, (i,j) -> (
	    if H#?{e1_j,i-1} then 
		H#{e1_j,i} = (-H#{e1_j,i-1}*H#{e0,i} + f_j*id_(F_i))//H#{e0,i+1}
		 else
		H#{e1_j,i} = (f_j*id_(F_i))//H#{e0,i+1}
	    )
	)
	    
peek H	
