Lift = method();
Lift(Matrix,Matrix,Matrix):= (f,g,h)-> ((q,r) := quotientRemainder (h*f,g);q)
Lift(ChainComplex,ChainComplex):=(F,G)->(
    f := map(F_0,G_0,id_(R^1));
    ll := {f};
    for i from 1 to length F do (
	f = Lift(G.dd_i,F.dd_i,f);
	ll = append(ll,f));
    g:=(i)->ll_i;
    map(F,G,g))

truncate(ChainComplex,ZZ):= (C,c) ->(ll := {}; 
for i from c to length C do ll = append(ll,C.dd_i);
chainComplex ll)

ghost = method();
ghost (ChainComplex):= (F)-> (
     P := R^0;out :={};mout:={};
     for i from 0 to length F do (
	  di := (directSum(F_i,P))_[0];
	  mout=append(mout,di);
	  Q := cover ker F.dd_i;
	  f := inducedMap(F_i,ker F.dd_i)*map(ker F.dd_i,Q,id_Q);
	  di = di* transpose (transpose (F.dd_(i+1))|| transpose (f));
	  out = append(out,di);
	  P = Q);
     fun:=i->if i <= length F then mout_i else (directSum(P,F_i))_[1];
     G:=chainComplex out;
     {G,map(G,F,fun)}
     )

isNull = (f)-> (
     out:=true;F:=target f;G:=source f;
     q:=(directSum(F_0,G_(-1)))_[1];i:=0;
     while out and (i<=length G) do (
	  (q,r) = quotientRemainder(f_i-q*G.dd_i,F.dd_(i+1));
     	  if image r != 0 then out = false else i = i+1);
     out)

level = (G)-> (
     n:=1;
     H:=ghost G;
     M:=H_1;
     while not isNull M do (
	  H = ghost H_0;
	  M = H_1*M;n=n+1);
     n)

	  
     
nonzeroc = (I)-> (G := koszul mingens I; ll := length G; 
     F := res (I,LengthLimit => ll);
     c := 0;
     f:= map(F_0,G_0,id_(R^1));
     for i from 1 to ll do(
	  f = Lift (G.dd_i,F.dd_i,f);
	  imf = image f;
	  M = image F.dd_(i+1);
	  if (imf +M)/M  !=0 then c = i);
     c)


