newPackage(
              "CompleteIntersectionResolutions",
              Version => "0.7", 
              Date => "Feb 2013",
              Authors => {{Name => "David Eisenbud", 
                        Email => "de@msri.org", 
                        HomePage => "http://www.msri.org/~de"}},
              Headline => "Analyzing Resolutions over a Complete Intersection",
	      PackageExports => {"BGG"},
              DebuggingMode => true
              )

	  export{
	   --some utilities
	   hf,
	   submoduleByDegrees,	   
	   submatrixByDegrees,
    	   toArray,
	   --things related to complete intersection resolutions
	   ExtModule, 
	   evenExtModule, 
	   oddExtModule,
	   ExtModuleData,
	   makeT,
	   isSurjCIOperator,
	   splittings,
	   splitResolution,
	   decomposeResolution,
	   cosyzygy,	  
	   matrixFactorization,
	   Check, -- optional arg for matrixFactorization
--	   BRanks,
	   Branks,
--	   BMatrices,
	   Bmats,
	   Amats,
	   mfBound,
	   highSyzygy,
	   Optimism, -- optional arg for highSyzygy
	   finiteBettiNumbers,
           infiniteBettiNumbers,
	   makeHomotopies,
	   makeHomotopies1,
           exteriorTorModule,
	   TateResolution,
	   makeModule,
	   isLinear,
	   freeExteriorSummand,
	   S2,
	   twoMonomials,
	   sumTwoMonomials,
	   moduleAsExt
	   }

truncate(ZZ, ChainComplex) := (i, GG) ->(
chainComplex(apply(length GG - i, j->GG.dd_(i+j+1)))
)

hf=(range, m)->(
       apply(range,i->hilbertFunction(i, m)))


ExtModule = method()
ExtModule Module := M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns   
     --Ext^*(M,(ring M)^1/(ideal vars ring M))
     --graded in POSITIVE degrees
     --as a module over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 2
     R := ring M;
     kk := coefficientRing R;
     kkk := (ring M)^1/(ideal vars ring M);
     E := Ext(M,kkk);
     TE := ring E;
     c := numgens source presentation R;
     X := local X;
     T := kk[X_0..X_(c-1), Degrees => toList(c:{2})];
     v := map(T,
	  ring E, 
	  vars T | matrix{toList ((numgens R):0_T)}, 
	  DegreeMap => i -> {-first i} );
     prune coker v presentation E)

///
restart
needsPackage "CompleteIntersectionResolutions"
  kk = ZZ/101
  S = kk[a,b,c]
  R = S/ideal"a2,b3,c4"
  M = R^1/ideal"a,b,c"
  E = ExtModule M
///


evenExtModule = method()
evenExtModule Module := M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns 
     --Ext^(even)(M,(ring M)^1/(ideal vars ring M))
     --as a module generated in degree 0
     --over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 1
     E := ExtModule M;
     P := positions(flatten degrees E, even);
     Ee:=prune image (E_P);
     T := ring E;
     kk:= coefficientRing T;
     X := symbol X;
     T1 := kk[X_0..X_(numgens T -1)];
     v1 := map(T1, T, vars T1, DegreeMap => i->{(first i)//2});
     coker v1 presentation Ee
     )


oddExtModule = method()
oddExtModule Module := M -> (
     --If M is a module over a complete intersection R
     --of codim c, the script returns 
     --Ext^(odd)(M,(ring M)^1/(ideal vars ring M))
     --as a module generated in degree 0
     --over the polynomial ring kk[X_1..X_(codim R)],
     --where the vars have degree 1
     E := ExtModule M;
     P := positions(flatten degrees E, odd);
     Eo:=prune image (E_P);
     T := ring E;
     kk:= coefficientRing T;
     X := symbol X;
     T1 := kk[X_0..X_(numgens T -1)];
     v1 := map(T1, T,vars T1, DegreeMap => i->{(first i)//2});
     coker v1 presentation Eo
     )

ExtModuleData = method()
ExtModuleData Module := M -> (
     --Suppose that M is a module over a complete intersection R
     --of codim c, so that 
     --E := ExtModule M 
     --is a module generated in degrees >=0 
     --over a polynomial ring T 
     --generated in degree 2, and
     --E0 := evenExtModule M and 
     --E1 := oddExtModule M
     --are modules generated in degree >= 0
     -- over a polynomial ring T' with generators 
     --in degree 1.
     --
     --The script returns 
     --{E0,E1,reg0,reg1}
     --where regi = regularity Ei
     --and prints a message if reg0 != reg1 
     --If we set r = max(2*reg0, 1+2*reg1),
     --and F is a resolution of M, then 
     --coker F.dd_(r+1)
     --is the first szygy module of M such that
     --regularity evenExtModule M =0 AND
     --regularity oddExtModule M =0 
     --We have been using regularity ExtModule M 
     --as a substitute for r,
     --but that's not always the same.
     E := ExtModule M;
     P0 := positions(flatten degrees E, even);     
     P1 := positions(flatten degrees E, odd);
     E0':=prune image (E_P0);
     E1':=prune image (E_P1);     
     T' := ring E;
     kk:= coefficientRing T';
     X := symbol X;
     T := kk[X_0..X_(numgens T' -1)];
     v1 := map(T, T' ,vars T, DegreeMap => i->{(first i)//2});
     E0 := coker v1 presentation E0';
     E1 := coker v1 presentation E1';
     r0 := max(0, regularity E0);
     r1 := max(0, regularity E1);
     --I've temporarily commented out the following because
     --of the bug in Ext (12/29/12)
{*     if abs(r0-r1)>1 then (
	 <<"regularities of even and odd Ext modules differ by more than 1" <<endl;
	 <<"module with presentation matrix" <<endl;
	 <<toString presentation M);
     *}
     {E0,E1,r0,r1}
     )
///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp ExtModuleData
viewHelp "CompleteIntersectionResolutions"
///
    

makeT = method()
makeT(Matrix, ChainComplex,ZZ) := (F,G,i) ->(
     {*
     If F is an m x 1 matrix and
     G is a resolution of a module at least up to the i-th step,
     over R = S/(ideal F), 
     of codim c this returns a list of the c ci-operators
     G_i \to G_{i-2}
     corresponding to the entries of F.
     *}
     c := numcols F;
     degsF := flatten((degrees F)_1);
     R := ring G;
     S := ring F;
     d0 := sub(G.dd_i, S);
     d1 := sub(G.dd_(i-1), S);
     Gtar := target d1;
     Gsour := source d0;
     d2 := d1*d0;
     utemp := local utemp;
     u := apply(c,i ->(
	     utemp = map(S^{-degsF_i}**Gtar, Gsour, d2//((target d2)**F_{i}));
	     d2 = d2 - utemp**F_{i};
	     utemp));
     --check: is d1*d0 = sum F_{i}*u_i 
     if d1*d0 != map(Gtar, Gsour, sum(c, i-> u_i**F_{i})) then 
                  error{"doesn't add up"};
     ret := map(R,S);
     apply(u, u1 -> ret u1)
     )

--ADDED Oct 30.
--the following is a still untested version keeping one of
--the differentials. We could just do it when
--the G complex is already decomposed, and use the lifting
--as a direct sum, and define the u0 map directly as a projection,
--but it may not matter.

--The plan: To get consistent t's, we'd do this for the top map in
--the complex, then use the components to define the other t's.

makeT(Matrix, ChainComplex,Matrix, ZZ) := (F,G,t0,i) ->(
     {*
     If F is a c x 1 matrix and
     G is a resolution of a module at least up to the i-th step,
     over R = S/(ideal F), 
     of codim c this returns a list of the c ci-operators
     G_i \to G_{i-2}
     corresponding to the entries of F,
     keeping t0 as the first of them.
     *}
     c := numcols F;
     degsF := flatten((degrees F)_1);
     R := ring G;
     S := ring F;
     d0 := sub(G.dd_i, S);
     d1 := sub(G.dd_(i-1), S);
     u0 := sub(t0,S);
     Gtar := target d1;
     Gsour := source d0;
     d2 := d1*d0;
     utemp := local utemp;
     u := apply(toList(1..c-1),i ->(
	     utemp = map(S^{ -degsF_i}**Gtar, Gsour, d2//((target d2)**F_{i}));
	     d2 = d2 - utemp**F_{i};
	     --assert(isHomogeneous utemp);
	     utemp));
     u = {u0}|u;
     --check: is d1*d0 = sum F_{i}*u_i 
     if d1*d0 != map(Gtar, Gsour, sum(c, i-> u_i**F_{i})) then error{"doesn't add up"};
     ret := map(R,S);
     apply(u, u1 -> ret u1)
     )

///
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
M = coker random(R^{0,-1}, R^{-2,-4,-5});
G = res(M, LengthLimit =>10)
assert(isHomogeneous ((makeT(F,G,5))_0))

r = isSurjCIOperator(F,G)
M = coker random(R^{0,-1}, R^{-2,-4,-5});
M = R^1/ideal"x2, yz"
high = 10
low = r-2 
E = decomposeResolution(F,G,low,10);
betti E
components E_10
(10-low)//2
A = new Array from 1..(10-low)//2
t0=E_10^A
T = makeT(F,E,t0,10);
T_0
T_1
--The components of E_i are numbered 0..(i-low)//2
--The sum of the first i components 
--is the kernel of the i-th iteration of t
--(where the t_low and t_(low+1) are replaced by 0).
--note that t:G_i-->G_(i-2)(-degf) is now the projection
--E_i^[1..#(components G_i)-1]
///

isSurjCIOperator = method()

isSurjCIOperator(Matrix, ChainComplex, ZZ) := (F,G,i) ->(
     {*
     Assuming that G is a resolution over a complete intersection
     S/ideal F with
     F = matrix{{f1, f2, ...}}
     returns "true" iff the operator G_i -> G_(i-2)
     "corresponding to f1" is surjective.
     *}
     v := (makeT(F,G,i))_0;
     0 == coker v
     )
isSurjCIOperator(Matrix, ChainComplex) := (F,G) ->(
     {*
     Assuming that G is a resolution over a complete intersection
     S/ideal F with
     F = matrix{{f1, f2, ...}}
     returns the smallest integer i
     so that the operator 
     G_j -> G_(j-2)
     "corresponding to f1" 
     is surjective for all i\leq j\leq length G.
     Question: is it enough to check this up to the regularity of 
     Ext?
     *}
     r := length G;     
     if not isSurjCIOperator(F,G,r) then return -1;
     for j from 0 to r-2 do
     	  if not isSurjCIOperator(F,G,r-j) then return r-j+1;
     2
     )


///
restart
loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
M = coker random(R^{0,-1}, R^{-2,-4,-5});
G = res(M, LengthLimit =>3)
isSurjCIOperator(F,G)
G = res(M, LengthLimit =>4)
isSurjCIOperator(F,G)
G = res(M, LengthLimit =>10)
isSurjCIOperator(F,G)
///

splittings = method()
splittings (Matrix, Matrix) := (a,b) -> (
     {*
     Assuming that (a,b) are the maps of a right exact
     sequence 
              a      b
     0--> A ----> B ----> C ----> 0 
     
     with B, C free,
--     the script produces a list {tau,sigma}
     the script produces a list {sigma, tau)
     sigma: B --> A a splitting of a and
     with tau: C --> B a splitting of b;
     that is
     a*sigma+tau*b = 1_B
     sigma*a = 1_A
     b*tau = 1_C
     *}
     if not isFreeModule source b then error("source b not free");
     if not isFreeModule target b then error("target b not free");
     (tau,remtau) := quotientRemainder(id_(target b),b);
     if remtau !=0 then error("second map not splittable");
     (sigma,remsigma) := quotientRemainder(id_(source b) - (tau*b),a);
     if remsigma !=0 then error("first map not splittable");
     {map(source a, target a, sigma), map(source b, target b,tau)}
     )


///
restart
loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[x,y,z]
t = random(S^{2:-1,2:-2}, S^{3:-1,4:-2})
t = id_(S^2)
betti t
isSurjective t
ss = splittings(syz t, t)
ss/betti

(A,B) = (syz t, t)
spl = splittings(A,B)
sigma = spl_0; tau=spl_1;
     assert(A*sigma+tau*B == id_(source B));
     assert(sigma*tau==0);
     assert(B*tau == id_(target B));
     assert(sigma*A == id_(source A));
///


splitResolution = method()
splitResolution(Matrix, ChainComplex, List) := (F,G,L)->(
     {*
     L is a list of integers corresponding 
     to spots in the resolution G over a complete
     intersection R = S/ideal F, where F = matrix{{f0..fn}}.
     Assumes that the operators
     t_i: G_i --> G_(i-2)
      corresponding to f0 are
     surjective for all i in L.
     computes s_i = ker t_i and splittings
     sigma_i: G_i --> source s_i
     tau_i : cover image t_i --> G_i
     returns the list of quadruples
     apply(L, i->
	  {s_i, sigma_i, tau_i,t_i}
	  )
    t,s,sigma, tau implements the decomposition of G, in the sense that:
    s_i = ker t_i, 
    sigma_i*s_i = 1, 
    t_i*tau_i = 1 (on G_(i-1) twisted by the degree of f0)     
    s_i*sigma_i + tau_i*t_i = 1_(G_i)
    sigma_i * tau_i = 0
     *}
     t := apply(L, i->(makeT(F,G,i))_0);
     --check whether the t's are surjective
     apply(#L, i-> if 0 != coker t_i then 
	  (print i;
	   error"operator not surjective at this stage"
	   ));
     --compute the maps decomposing the resolution relative 
     --to t_i for i in L.
     s := apply(#L, i-> map(source t_i, , syz t_i));
     --assert(isHomogeneous s_0);
     Si := {};
     splits := apply(#L, i->(Si = splittings(s_i,t_i);
	       assert(Si_0*s_i == id_(source s_i)); -- Si_0 == sigma_i
	       assert(t_i*Si_1 == id_(target t_i)); -- Si_1 == tau_i
	           {s_i, Si_0, Si_1,t_i}));
     splits
     )

--The following versio takes the low and high elements of L,
--returns a list where only the indices low to high are set,
--the others === null.
splitResolution(Matrix, ChainComplex, ZZ,ZZ) := (F,G,low, high)->(
     L := toList(low..high);
     s := new MutableList from {};
     ss := splitResolution(F,G,L);
     scan(L, i->s#i = ss_(i-low));
     toList s)



///
restart
loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
M = coker random(R^{0,-1}, R^{-2,-4,-5});
G = res(M, LengthLimit =>10)
ss1 = splitResolution(F,G,toList(5..7))
ss = splitResolution(F,G,5,7)
#ss
assert (ss1_0==ss_5)

///

decomposeResolution = method()
decomposeResolution(Matrix, ChainComplex,ZZ,ZZ) :=(F,G,low, high) ->(
{*   F=matrix{{f0..fn}} is a matrix of a regular sequence in a poly ring S.
     G is a resolution over R:=S/ideal F.
     G_lower and G_upper are modules in the resolution G such that
     f_0 defines a surjective
     ci-operator t_i: G_i > G_(i-2) for each i = low+2..high.
     (Really this is the CI operator defined by f1..fn.)
     (thus low must be at least isSurjCIOperator(F,G) -2.)

     The script computes
     s_i: ker t_i > G_i 
     and chooses splittings
     sigma_i: G_i > ker t_i

     Setting K_i = source s_i = ker t_i,
     we thus have G_i \cong K_i ++ K_(i-2) ++...
     The script returns a copy E of the complex G
     written in terms of this splitting,
     so that the map K_(i-2j) > K_(i-1-2m) induced by G.dd_i
     is (E.dd_i)^[j]_[m]. In particular, the map t:G_i>G_(i-2)
     becomes
     (E.dd_i)^[1,2,..]
     
     The components of E_i are numbered 0..(i-low)//2
     The sum of the first i components 
     is the kernel of the i-th iteration of t
     (where the t_low and t_(low+1) are replaced by 0).
*}
     R := ring G;
     degf := (degree (flatten entries F)_0)_0;
     L := toList(low+3..high);
     L0 := toList(low+2..high);     
     L1 := toList(low..high);
     L2 := toList(low+1..high);     
     ss := splitResolution(F, G, low+2, high);
--returns list of quadruples {s,sigma,tau,t}
--with s = ker t, sigma a splitting of s and tau a splitting of t.

     s := new MutableList from {};
     sigma := new MutableList from {};
     t := new MutableList from {};
     scan(L0, i-> (
	  s#i=ss_i_0;
          sigma#i = ss_i_1;
	  t#i = ss_i_3));

--make a list of the building blocks of the resolution,
--which are the kernels of the operators t corresponding to f0
     K := new MutableList;
     K#(low) = G_(low); 
     sigma#(low) = id_(K#(low));
     K#(low+1) = G_(low+1);
     sigma#(low+1) = id_(K#(low+1));
     scan(L0, i-> K#i = source s#i); 

--now form the free modules
     GG := new MutableList from {};
     GG#(low) = R^{-low}**K#low;
     GG#(low+1) = R^{-low}**K#(low+1);
     scan(L0, i-> GG#i = 
	 directSum apply(toList(0..(i-low)//2),
	       j->R^{ -low-j*degf}**K#(i-2*j))
	       );
	  
--and the maps that will be isomorphisms from old to new
     iso:= new MutableList from {}; 
     maplist :={};
     mati := local mati;
     iso#(low) = id_(GG#(low));
     iso#(low+1) = id_(GG#(low+1));	  
     scan(L0, i-> (maplist = apply(toList(0..(i-low)//2),
		    j->(
		    (sigma#(i-2*j))*
		    product apply (toList(0..j-1),m->
			 t#(i-2*(j-1)+2*m))));
	       	    mati = maplist_0;
		    for u from 1 to #maplist-1 do mati = 
		        mati || maplist_u;
	            iso#i = map(GG#i, G_i,mati))
	       );
	  
--finally, move the differential to the new resolution
--via the isomorphisms.
     H := chainComplex apply(L2,
	  i->(iso#(i-1))*G.dd_i*((iso#i)^(-1)));
     H[-low]
    )
///
restart
loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
M = coker random(R^{0,-1}, R^{-2,-4,-5});
M = R^1/ideal"x2, yz"
high = 10
G = res(M, LengthLimit =>high)
r = isSurjCIOperator(F,G)
low = r-2
E = decomposeResolution(F,G,low,10);
betti E 
betti G
betti E == betti truncate(low,G)

--The components of E_i are numbered 0..(i-low)//2
for i from low to high do
    assert(#components E_i == ((i-low)//2)+1)
--The sum of the first i components 
--is the kernel of the i-th iteration of t
--(where the t_low and t_(low+1) are replaced by 0).

#components E_9
--component({1},{0}, E.dd_10)
E.dd_10

(E_7)_[0]--inclusion of the kernel of t
(E_6)^[1]--projection to first factor, in this case = t.
(E_10)_[0,1,2] -- kernel of the third iterate t^3: E_10 -> E_4
--note that t:G_i-->G_(i-2)(-degf) is now the projection onto
--E_i^[1..#(components G_i)-1]
-- also, each differential is an explicit component of the one
--two steps further up.
for i from 5 to 10 do assert(
(R^{ -3}**E.dd_(i-2))==
E_(i-1)^(splice[(1..#(components E_(i-1))-1)])*
   ((E.dd_i)*
     ((E_i)_(splice[(1..#(components E_i)-1)])))
)
--further, the sub-diagonal blocks of the differential are zero
betti E.dd_i
betti (R^{ -3}**E.dd_(i-2))
for p from 0 to #components E_10 -1 do 
     for q from 0 to p-1 do
     assert (0==component({p}, {q}, E.dd_10))
///


toArray = method()
toArray List := L -> splice [toSequence L]
toArray ZZ := n->[n]


///
component = method()
component(List, List, Matrix) := (Ltar, Lsour, m) ->(
     {*Checks that m is a map between direct sum modules
     with components corresponding to the elements of Ltar
     and Lsour, and returns the submatrix corresponding to
     those components.
     *}
     cs := components source m;
     ct := components target m;
     if min Lsour<0 or max Lsour > #cs-1 then
          error"not enough components in source";
     if min Ltar<0 or max Ltar > #ct-1 then 
          error"not enough components in target";     
     ((target m)^(toArray Ltar)) * m * ((source m)_(toArray Lsour))
     )
///


///
toArray 5
toArray {3,5,6}
toArray {a,b,c}

kk= ZZ/101
S = kk[x,y,z]
A= (matrix"x2"|matrix"xy")||matrix"y2"|matrix"2x2"
B = map(S^1++S^1, S^{-2}++S^{-2}, A)
component({1},{0,1},B)
truncate(ZZ, ChainComplex) := (low, G) -> (
     GG := chainComplex apply(toList(low+1..length G), i->G.dd_i);
     (ring G)^{-low}**GG[-low])
///



///
restart

loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
M = coker random(R^{0,-1}, R^{-2,-4,-5});
--M = R^1/ideal"x2, yz"
high = 10
G = res(M, LengthLimit =>high)
r = isSurjCIOperator(F,G)
low = r-2
betti truncate(low, G)
betti G
E = decomposeResolution(F,G,low,10);
///



transpose Module := M -> coker transpose presentation M
    --this is Auslanders transpose functor
    
cosyzygy = method()
cosyzygy (ZZ,Module) := (p,M)-> (
    --returns a p+1-step resolution F of the 
    --p-th cosyzygy of M (so F.dd_p is the presentation
    --matrix of M.) 
    --This is zero if the module
    --is annihilated by a nonzerodivisor. Makes most sense for
    --and MCM over a Gorenstein ring.
    E:=res (transpose M, LengthLimit => p+1);
    chainComplex apply(p+1, j->transpose E.dd_(p+1-j))
    )
	     
cosyzygy Module := M -> cosyzygy(2,M)
///
restart
loadPackage "CompleteIntersectionResolutions"

--Example3
S = kk[a,b,c]
ff = (vars S)^[3]
ff1 = random(S^1, S^{3: -1})
R = S/ideal ff; 
M0= R^1/ideal"ab"
regularity ExtModule M0
len = 14
betti (FF = res(M0, LengthLimit => len)) 
M = coker (FF.dd_len)
betti presentation M
betti ((cosyzygy(2, M)).dd_3)
betti (cosyzygy(2, M))
///

matrixFactorization = method(Options=>{Check => true})
matrixFactorization(Matrix, Module) := opts -> (ff, M) -> (
    --Inputs:
    --ff = {{f1,..,fc}} is a 1 x c matrix 
    --whose entries are a sufficiently 
    --general regular sequence in S.
    --R#c := S/(ideal ff).
    --M an R#c-module that is a high syzygy over R#c.
    --
    --If opts#check == true (the default value) then various
    --tests are performed along the way.
    
    --Outputs: 
    --d: a triangular map of direct-sum modules,
    --the matrix factorization differential.
    --
    --h: a hashTable where the h#p are maps of direct sum modules.
    --the partial homotopies.
    --
    --Description:
    --Atar#p = (target BS#1++..++target BS#p) 
    --Asour#p = (source BS#1++..++source BS#p), and
    --
    --d: Atar#c <-- Asour#c
    --and h#p: Asour#p <--- Atar#p over S.
    --The map
    --d is a special upper triangular 
    --lifting to S of the presentation matrix
    --of M over R#c.
    --
    --The map h#p is a homotopy for ff#p on the restriction
    --dpartial#p: Atar#p <-- Asour#p of d, over the ring R#(p-1),
    --so dpartial#p * h#p = ff#p mod (ff#1..ff#(p-1).
    --
    --In addition, h#p * dpartial#p induces f#p on B1#p.
    --
    --Notation:
    --B1#i is the i-th matrix (ie, complex) 
    --of the matrix factorization tower,
    --regarded as a map over R#(i-1);
    --A#(p-1) is the matrix over R#p obtained inductively
    --as the induced map on the complex
    --ker A1#(p) -->> B1#(p), where A1#p is A#p lifted to R#(p-1).
    --inc#(p,0): source A#(p-1) \to source A#p -- inclusion
    --inc'#(p,0): splits inc#(p,0)
    --inc#(p,1) and inc'#(p,1): same for targets
    --proj#(p,0):source A1#p -->> source B1#p
    --proj'#(p,0):its splitting
    --proj#(p,1), proj'#(p,1): same for targets.
    
--Initialize local variables
    spl:= null; -- a dummy variable for splittings
    h := new MutableHashTable;
    A := new MutableHashTable;
    A1 := new MutableHashTable;
    --A1#p is A#p substituteed into R#(p-1)
    B1 := new MutableHashTable;
    --B1#p would be B#p over R#(p-1) (there is no B)
    BS := new MutableHashTable; --same over S
    dpartial := new MutableHashTable;    
    psi:= new MutableHashTable;--psi#p: B1#p-->target A#(p-1)
    psiS:= new MutableHashTable;--psi#p: B1#p-->target A#(p-1)    
    inc := new MutableHashTable; --the #p versison are over R#(p-1)
    inc' := new MutableHashTable;    
    inc'S := new MutableHashTable;        
    proj := new MutableHashTable; 
    projS := new MutableHashTable;     
    proj' := new MutableHashTable;
    E := null; -- cosyzygy complex over R#p
    E1 := new MutableHashTable;
    --E1#i will be E.dd_i substituted into R#(p-1)
    
--Substance begins HERE.
    fail := false; --flag to escape if a CI op is not surjective    
    --Put the regular sequence and the factor rings into hash tables:
    --ci#i is the i-th element; R#i is codim i.
    c := numcols ff;
    S := ring ff;
    ci := hashTable apply(toList(1..c), 
	 p->{p,ff_{p-1}});--values are 1x1 matrices
    degs := hashTable apply(toList(1..c), 
	p->{p,(degree ci#p_0_0)_0});--values are ZZ
    R := hashTable apply(toList(0..c), 
	p->(if p==0 then {0,S}
	    else {p,S/ideal apply(toList(1..p), j->ci#(j))}));

--MAIN LOOP: work from p = c down to p = 1, creating the B1#p etc
    A#c = presentation M; --initialize
scan(reverse toList(1..c), p->(
    E = cosyzygy(2, coker A#p);	
    --sub into R#(p-1)
    A1#p = substitute (A#p, R#(p-1));
    scan(toList(1..3), i->E1#i = sub(E.dd_i,R#(p-1)));
    --define the ci operators proj#(p,j), A1#c --> B#c
    --and their kernels inc#(p,j) over R#(c-1).
    scan(2, j->(
	proj#(p,j) = map(R#(p-1)^{ -degs#p}**target E1#(j+1),
	                 source E1#(j+2),
			 E1#(j+1)*E1#(j+2)//((target E1#(j+1)**ci#p)));
        inc#(p,j) = syz proj#(p,j)
	));
    --if one of the proj#(p,j) is not surjective then
    --set fail = true and break from loop
    scan(2,j->
	if not isSurjective proj#(p,j) then(
	   << "CI operator not surjective at level codim " << c << endl;
	   << "on example M = coker "  << endl;
	   <<toString presentation M <<endl;
	   fail = true;
	   break;
	 ));
    if fail == true then break;
    --make the splittings to/from A1#p, over R#(p-1)
    scan(2, j-> (
         spl :=splittings(inc#(p,j),proj#(p,j));
         inc'#(p,j) = spl_0;
         proj'#(p,j) = spl_1));
   --make B1#p, A#(p-1), and
   --the map psi#p: source B1#p -> target A1#(p-1)
         B1#p = proj#(p,0)*A1#p*proj'#(p,1); -- B#p over R#(p-1)
         A#(p-1) = inc'#(p,0)*A1#p*inc#(p,1);
         psi#p = inc'#(p,0)*A1#p*proj'#(p,1);
));
--END OF MAIN LOOP
--Now put together the maps for output. All the work is done except
--for the creation of the homotopies.
    if fail == true then return("cannot complete MF");
    --lift all the relevant maps to S
    scan(toList(1..c), p-> (
	    BS#p = substitute(B1#p, S);
	    psiS#(p)= substitute(psi#p, S);
	    scan(2, j->(
	    projS#(p,j)= substitute(proj#(p,j), S);
	    inc'S#(p,j)= substitute(inc'#(p,j), S)
	        ))
	    ));
    --make psi(q,p):  BS#(q,0) <-- BS#(p,1) (note direction!)
    scan(toList(1..c), p->scan(toList(1..c), q->(
	    if q>p then psi#(q,p) = map(target BS#q,source BS#p, 0)
	    else if q == p then psi#(q,p) = BS#p
	    --if q< p then psi#(q,p) is a composition of
	    --a projection and a sequence of inclusions.
 	    else if q<p then( 
	     spl = psiS#p;
	     scan(reverse toList(q+1..p-1), j -> 
		 spl = inc'S#(j,0)*spl);
	     psi#(q,p) = projS#(q,0)*spl
	     )
    	    )));
    --construct the triangular differential d:Asour --> Atar, 
    --first as a list of lists of matrices
    Atar := directSum(apply(toList(1..c), p->target BS#p));
    Asour := directSum(apply(toList(1..c), p->source BS#p));    
    LL := apply(toList(1..c),
	       q->apply(toList(1..c), 
	       p->psi#(q,p)));
    d := map(Atar, Asour, matrix LL);

    --make homotopies h#p for ci#p on A1#p.
    --BUG: tensoring with R#(p-1) destroys the cache of components
    --of a direct sum, so
    --define dpartial#p over S, to be 
    --the restriction of d to the first p summands.
    scan(toList(1..c), p->(
    dpartial#p = map(
        target Atar^(toArray toList(0..p-1)),
        source Asour_(toArray toList(0..p-1)),
        Atar^(toArray toList(0..p-1))*
        d*
        Asour_(toArray toList(0..p-1)));
	       
    h#p = map(source dpartial#p, 
        S^{ -degs#p}**target dpartial#p,
        substitute(
        (R#(p-1)**(target dpartial#p**ci#p))//
                        (R#(p-1)**dpartial#p),
		   S));

--optionally check that dpartial and h have the right relationship
   if opts#Check==true then(
   if not isHomogeneous h#p 
         then error "homotopy not homogeneous";
   if 0 != R#(p-1)**dpartial#p*h#p - 
      R#(p-1)**(target dpartial#p)**ci#p
         then error "homotopy not good";
   if 0!= R#(p-1)**(target h#p)^[p-1]*h#p*dpartial#p- 
                 R#(p-1)**(target h#p)^[p-1]**ci#p
            then error "homotopy on B not good";   
                           )
    	));
--H = flatten apply(#h, p->(source d)h#p
--(source d)_[0,1]*H#2
{d,hashTable pairs h}
)

Branks = method()
Branks List := MF -> (
      B0 := (target MF_0).cache.components;
      B1 := (source MF_0).cache.components;
      apply(#B0, i-> {rank B0_i, rank B1_i}
      ))
--BRanks = BRanks

Bmats = method()
Bmats List := MF -> (
    	d := MF_0;
        apply(#Branks MF, i-> (
	(target d)^[i]*d*(source d)_[i]))
        )
Amats = method()
       Amats List := MF -> (
               d := MF_0;
               apply(#Branks MF, i-> (
               (target d)^(toArray toList(0..i))*d*(source d)_(toArray toList(0..i))))
               )
    
mfBound = method()
mfBound Module := M0 ->( 
    --gives (conjectural) bound for which map in the resolution
    --of M0 will have cokernel a high syzygy
E := ExtModuleData M0;
1+max(2*E_2, 1+2*E_3)
)

highSyzygy = method(Options=>{Optimism => 0})
highSyzygy Module := opts -> M0 ->(
    --with increment => 0 (the default) this gives our conjectural
    --bound, which is best possible.
    -- But if that's not good enough, use Optimism=>-1 etc
    len := mfBound M0-opts#Optimism;
    F := res(M0, LengthLimit => len);
    coker F.dd_len)

///%%

restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
--viewHelp matrixFactorization
--Example 0
S = kk[a,b]
ff = matrix"ab"
R = S/ideal ff
M0 = R^1/ideal"a,b"
regularity ExtModule M0 -- 2
len = 2
F = res(M0, LengthLimit =>len)
--
MF = matrixFactorization(ff,coker F.dd_len)
MF = matrixFactorization(ff,coker F.dd_len,Check=>false)
MF = matrixFactorization(ff,highSyzygy M0)
betti MF_0
betti MF_1#1
MF_0*MF_1#1
BRanks MF

--Example 0a
S = kk[a,b,c]
ff = matrix"ac-b2"
R = S/ideal ff
m = matrix"a,b;b,c"
betti m
M0 = coker m
MF = matrixFactorization(ff,highSyzygy M0)
BRanks MF

--Example1
S = kk[a,b,u,v]
ff = matrix"au,bv"
R = S/ideal ff
M0 = R^1/ideal"a,b"
MF = matrixFactorization(ff,highSyzygy M0)
BRanks MF

--Example2
S = kk[a,b]
ff = (vars S)^[3]
R = S/ideal ff;
M0=R^1/ideal"ab" 
MF = matrixFactorization (ff, highSyzygy M0)
Branks MF

--Example3
S = kk[a,b,c]
ff = matrix"a3,b3,c3"
betti ff
ff1 = ff*random(S^{3: -3}, S^{3: -3})
R = S/ideal ff; 
M0= R^1/ideal"ab"
MF = matrixFactorization (ff1, highSyzygy M0)
netList Branks MF

--Example4
S = ZZ/101[a,b,c,d]
mm= ideal vars S
ff = (matrix"a3,b3,c3,d3")
ff1 = ff*random(source ff, source ff);
R = S/(ideal ff);
M0 = coker map(R^1, R^{-2,-3}, matrix"a2,bcd")
MF = matrixFactorization(ff1,highSyzygy M0);
netList Branks MF

--Formerly bad example. Now seems fine
S = ZZ/32003[x_0..x_2]
f = matrix{{x_0^5, x_1^5, x_2^5}}
ff = f*random(source f, source f)
R = S/ideal f
m1 = {x_0^2*x_2^4, x_0*x_1^4*x_2}
M0 = R^1/ideal(m1_0+m1_1);
MF = matrixFactorization(ff, highSyzygy M0);
netList BRanks MF
///


finiteBettiNumbers = method()
finiteBettiNumbers List := MF -> (
    --MF should be the output of  matrixFactorization
    B := Branks MF;
    c := #B;
     sourceRanks := B/last;
     targetRanks := B/first;
     apply(c+1, j->
           sum(1..c, 
	     i-> (targetRanks_(i-1)*binomial(i-1,j)+
		  sourceRanks_(i-1)*binomial(i-1,j-1))
	     ))
     )

infiniteBettiNumbers = method()
infiniteBettiNumbers (List,ZZ) := (MF,len) -> (
    --MF should be the output of  matrixFactorization
    B := Branks MF;
    c := #B;
     sourceRanks := B/last;
     targetRanks := B/first;
     apply(len+1, j->
	 if j%2 ==0 then
           sum(1..c, 
	     i-> (targetRanks_(i-1)*binomial(c-i+j//2,c-i)))
	 else
           sum(1..c, 
	     i-> (sourceRanks_(i-1)*binomial(c-i+(j-1)//2,c-i)))
	     )
     )
///
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
///

     
///
restart
loadPackage("CompleteIntersectionResolutions", Reload => true)
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp finiteBettiNumbers
///
    


{*
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp CompleteIntersectionResolutions
viewHelp exteriorTorModule
*}   






show01 = (f,G,L) -> (
     --f is a matrix of a regular sequence in a poly ring S.
     --G is a resolution over R:=S/ideal f.
     --L is a list of consecutive
     --    indices in the resolution G, 
     --    in increasing order
     --f_0 should be sufficiently generic to define a surjective
     --ci-operator t_i: G_i --> G_(i-2) for each i in L.
     --the script chooses splittings G_i = ker t_i ++ F_i
     --returns a list D01 of the 01-blocks of the
     -- differentials at the spots
     --in L
     --  d_^(0,1): F_i --> G_(i-1) (for i in L' = drop(1,L))
     --and a list T of the similar corner for the ci-operator
     --corresponding to the second element in f 
     -- for i in L'' = drop(1,L')
     fList := flatten entries f;
     if #L <=2 then error"not enough integers in L";
     L' := drop(L,1);
     L'':= drop(L',1);
     ss := splitResolution(fList_0, G, L);
     T := apply(L, i->makeT(f,G,i));
     d := apply(L, i-> G.dd_i);
     sigma := local sigma;
     tau := local tau;
     D01 := apply (#L-1, i-> (
	       sigma = ss_i_1;
	       tau = ss_(i+1)_2;
	  sigma*d_(i+1)*tau));
     T01 := apply (#L-2, i-> (
	       	      sigma = ss_i_1;
	              tau = ss_(i+2)_2;
                      sigma*(T_(i+2))_1*tau));
     (D01,T01)
     )

///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"

restart
loadPackage "CompleteIntersectionResolutions"
kk = ZZ/101
S = kk[x,y]
f = matrix"x2y, x3+y3"
f1 = (flatten entries f)_0
R = S/ideal f
kkk=coker vars R
G = res(kkk, LengthLimit => 10)
decomposeResolution(f1, G, 3)
splitResolution(f1, G, {3,4,5,6,7})
(D,T) = show01(f,G,{3,4,5,6,7})
D
T
restart
loadPackage "CompleteIntersectionResolutions"
kk = ZZ/101
S = kk[x,y,z]
f = matrix"x3+y3, x2y, z3"
R = S/ideal f
m= ideal vars R
M = R^1/(m^2)
M = coker random(R^{0,-1}, R^{-2,-4})
G = res(M, LengthLimit => 7)
betti G
(D,T) = show01(f,G,{5,6,7})
D
T
///




///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp S2
viewHelp splittings
viewHelp makeHomotopies
viewHelp CompleteIntersectionResolutions
restart
loadPackage "CompleteIntersectionResolutions"
S = kk[a,b]
R = S/ideal"a3,b3"
N = R^1/(ideal vars R)
FN = res (N, LengthLimit => 5)
A = res coker FN.dd_5
betti FN
betti extend A
--note: to get the degree of a generator shown by betti you have to 
--add the column label (NOT the column position) to the row label
betti FN.dd_3
///


--The following functions are used in makeHomotopies
expo = method()
expo(ZZ,ZZ) := (n,d) ->(
     --the next three lines define a function that returns
     --a list of all lists of n non-neg ints adding up to d.
     x:=local x;
     T := ZZ/2[x_0..x_(n-1)];
     flatten((flatten entries basis(d, T^1))/exponents)
     )

lessThan = (L1,L2) -> (
     --returns true if L1<L2 in the termwise partial order
     for i from 0 to #L1-1 do if L1#i>L2#i then return false;
     if L1==L2 then return false
     else return true)
    

expo(ZZ,List):= (n,L) ->(
     --returns the list of all elements of expo(n,d) that
     --are <L in the termwise partial order
     d := sum L;
     LL := flatten(for i from 0 to d-1 list expo(n,i));
     select(LL, M->lessThan(M,L))
     )

makeHomotopies = method()
makeHomotopies (Matrix, ChainComplex) := (f,F) ->
     makeHomotopies(f,F, max F)


     
makeHomotopies (Matrix, ChainComplex, ZZ) := (f,F,d) ->(
     --given a 1 x lenf matrix f and a chain complex 
     -- F_min <-...,
     --the script attempts to make a family of higher homotopies
     --on F for the elements of f.
     --The output is a hash table {{i,J}=>s), where
     --J is a list of non-negative integers, of length = ncols f
     --and s is a map F_i->F_(i+2|J|-1) satisfying the conditions
     --s_0 = d
     -- s_0s_{i}+s_{i}s_0 = f_i
     -- and, for each index list I with |I|<=d,
     -- sum s_J s_K = 0, when the sum is over all J+K = I
     H := new MutableHashTable;
     minF := min F;
     maxF := max F;
     if d>max F then d=maxF;
     flist := flatten entries f;
     lenf := #flist;
     e0 := (expo(lenf,0))_0;
     for i from minF to d+1 do H#{e0,i} = F.dd_i;

     e1 := expo(lenf,1);
     scan(#flist, j->H#{e1_j,minF-1}= map(F_minF, F_(minF-1), 0));
     for i from minF to d do
	       scan(#flist,
	       j->H#{e1_j,i}= (-H#{e1_j,i-1}*H#{e0,i}+flist_j*id_(F_i))//H#{e0,i+1}
	       );
     for k from 2 to d do(
	  e := expo(lenf,k);
	  apply(e, L ->(
	    k := sum L;
	    H#{L,minF-1}= map(F_(minF+2*k-2),F_(minF-1),0);
	    for i from minF to d-2*k+1 do
	      H#{L,i} = sum(expo(lenf,L), 
		 M->(H#{L-M,i+2*sum(M)-1}*H#{M,i}))//H#{e0,i+2*k-1};
	    )));
     hashTable pairs H
     )

makeHomotopies1 = method()
makeHomotopies1 (Matrix, ChainComplex) := (f,F) ->(
     makeHomotopies1 (f,F, length F))

makeHomotopies1 (Matrix, ChainComplex, ZZ) := (f,F,d) ->(
     --given a 1 x lenf matrix f and a chain complex 
     -- F_min <-...,
     --the script attempts to make a family of first homotopies
     --on F for the elements of f.
     --The output is a hash table {{J,i}=>s), where
     --J is an integer 0<= J < lenf, 
     --and s is a map F_i->F_(i+1) satisfying the conditions
     -- ds_{i}+s_{i}d = f_i
     H := new MutableHashTable;
     minF := min F;
     maxF := max F;
     if d>max F then d=maxF;
     flist := flatten entries f;
     rem := 0; -- no error yet.
     h := null;
     scan(#flist, j->H#{j,minF-1}= map(F_minF, F_(minF-1), 0));
     for i from minF to d do
	       scan(#flist, j->(
	       (h,rem) = 
	          quotientRemainder(-H#{j,i-1}*F.dd_i+flist_j, --*id_(F_i),
		                   F.dd_(i+1));
	       if rem != 0 then (
		     <<"homotopy " <<{j,i} <<" doesn't exist."<<endl;
		     --error()
		     );
	       H#{j,i} = h;    
	       ));
     hashTable pairs H
     )


///
restart
loadPackage("CompleteIntersectionResolutions", Reload =>true)
kk=ZZ/101
S = kk[a,b,c]
F = res ideal vars S  
f = matrix{{a,b,c}}
H = makeHomotopies1(f,F)
homot = makeHomotopies(f,F,2)
homot = makeHomotopies(f,F,1)
peek homot
netList select(keys homot, k->homot#k!=0)


f = matrix{{a^3,b^4}}
F= res (ideal vars S)
F = res ideal"a4,b2"
H = makeHomotopies1(f,F,3)
netList select(keys H, k->H#k!=0)
///


exteriorTorModule = method()
exteriorTorModule(Matrix, ChainComplex) := (f,F) -> (
     --Write Tor_S(M,k) as a module over Tor(S/(f),k) = \wedge V:
     --f is a matrix with entries that are homotopic to zero on F
     --Typically, F is a resolution of a module annihilated by
     --the entries of f.
     H := makeHomotopies1(f,F);
     flist := flatten entries f;
     lenf := #flist;
     k := coefficientRing ring F;
     T := toList apply(min F..max F,i->sub(F_i,k));
     Hk := hashTable apply(keys H, h-> (h, sub(H#h,k)));
     --Hk(j,i) is the homotopy for f_j from F_i**k to F_(i+1)**k,
     --defined for i from min F to max F-1.
     e := symbol e;
     E := k[e_0..e_(numcols f -1), SkewCommutative => true];
     TE :=makeModule(E,T,Hk);
     print TateResolution TE;
     TE
)	  

makeModule = method()
makeModule(Ring,List,HashTable) := (R,T,Hk) -> (
     --T is a list of free modules F_i over over
     --k =  coefficientRing R.
     --H is a HashTable with pairs of the form {j,i} => phi,
     --where phi: F_i\to F_(i+1).
     --The script takes R**\sum F_i as a graded R-module, 
     --where the j-th generator of R acts as H#{j,i}.
     k := coefficientRing R;
     pro := map(R,k);
     RT := apply(#T, i->pro(T_i)**R^{ -i});
     P := directSum RT;
     RHk := hashTable apply(keys Hk,ke ->(
	       i := last ke;
	       j := first ke;
	       (ke, map(RT_(i+1), RT_i**R^{ -1},pro Hk#{j,i})))
	       );
     M := P/sum apply(keys Hk,ke ->(
	       i := last ke;
	       j := first ke;
	       image(P_[i+1]*RHk#{j,i}-R_j*P_[i])));
     --prune M
     M
     )

isLinear = method()
isLinear(Matrix) := phi ->(
     L := (flatten entries phi)/degree;
     flag := true;
     scan(flatten L, ell-> if ell>1 then (flag = false;break));
     flag)


freeExteriorSummand = method()
freeExteriorSummand(Module) := M -> (
     --M should be a module over an exterior algebra E.
     --script finds a basis of M/(ann_M soc E).
     E := ring M;
     mm := ideal vars E;
     soc := (ideal 0_E):mm;
     nongens := (0_E*M):soc;
     freegens := (basis (M/nongens))//inducedMap(M/nongens,M)
     )
///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp "CompleteIntersectionResolutions"
///
///
restart
loadPackage( "CompleteIntersectionResolutions", Reload => true)
kk= ZZ/101
E = kk[e,f,g, SkewCommutative => true]
M = E^1++module ideal vars E++E^{-1}
freeExteriorSummand M


kk=ZZ/101
S = kk[a,b,c]
F = res (ideal vars S)
f = matrix{{a,b,c}}
H = makeHomotopies1(f,F)
tor = exteriorTorModule(f,F)

betti tor
betti prune tor

f = gens ideal"a3,b3,c3"
R = S/ideal f
M = R^1/(ideal"abc,a2b")
betti (FF =res( M, LengthLimit =>8))
p = map(R,S)
MS = prune pushForward(p, coker FF.dd_3)
betti(F = res MS)
T = exteriorTorModule(f,F);
betti T
betti (PT = prune T)
phi = presentation PT
isLinear phi

M= coker random(R^2, R^{3:-1})
betti (FF =res( M, LengthLimit =>10))
p = map(R,S)
MS = prune pushForward(p, coker FF.dd_4);
--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
T = exteriorTorModule(f,F);
betti T
betti (PT = prune T)
phi = presentation PT;
isLinear phi
submatrixByDegrees(phi,{0},{2})

S = kk[a,b,c,d]
f = (vars S)^[3]
R = S/ideal f
p = map(R,S)
--M= coker random(R^2, R^{3:-1}) -- too hard!
M = R^1/ideal"ab+cd+b2+d2,abc"
M = coker random(R^1, R^{-2})
time betti (FF =res( M, LengthLimit =>6))
MS = prune pushForward(p, coker FF.dd_4);
--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
time T = exteriorTorModule(f,F);
betti T
betti (PT = prune T)
phi = presentation PT;
isLinear phi
submatrixByDegrees(phi,{0},{2})

S = kk[a,b,c,d]
f = (vars S)^[4]
R = S/ideal f
p = map(R,S)
--M= coker random(R^2, R^{3:-1}) -- too hard!
M = R^1/ideal"a2b+bc2,ac+b2,c3d3"
--M = coker random(R^1, R^{-2})
time betti (FF =res( M, LengthLimit =>6))
MS = prune pushForward(p, coker FF.dd_4);
--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
time T = exteriorTorModule(f,F);
betti T
betti (PT = prune T)
phi = presentation PT;
isLinear phi
submatrixByDegrees(phi,{0},{2})



///

--load "HomMatrixModule.m2" -- still necessary in 1.5?


S2 = method()
S2(ZZ,Module) := Matrix => (b,M)-> (
     --returns a map M --> M', where M' = \oplus_d>=b H^0(\tilde M).
     --the map is equal to the S2-ification AT LEAST in degrees >=b.
     S := ring M;
     r:= regularity M;
     if b>r+1 then return id_(truncate(b,M));
     tbasis := basis(r+1-b,S^1); --(vars S)^[r-b];
     t := map(S^1, module ideal tbasis, tbasis);
     s:=Hom(t,M)
     --could truncate source and target; but if we do it with
     --the following line then we get subquotients AND AN ERROR!
--     inducedMap(truncate(b,target s),truncate(b,source s),s)
     )

///
restart
loadPackage "CompleteIntersectionResolutions"
S = kk[a,b,c]
M = truncate(3,S^1)
f = inducedMap(S^1,M)
hf(0..10,coker S2(0,M))
betti S2(1,M)


S = kk[a,b,c,d]
M = S^1/intersect(ideal"a,b,c", ideal"b,c,d",ideal"c,d,a",ideal"d,a,b")
prune source S2(0,M)
prune target S2(0,M)
hf(-5..5,coker S2(-5,M))


S = kk[a,b,c,d]
M = truncate(3,S)
betti S2(0,M)
betti S2(1,M)
M = S^1/intersect(ideal"a,b,c", ideal"b,c,d",ideal"c,d,a",ideal"d,a,b")
S2(0,M)

S = kk[a,b]
M = coker map(S^2, S^{2:-1}, matrix"a,b;0,0")
betti S2(-1,M) -- this is wrong (also with 0)

S=kk[a,b,c]
I = ideal (vars S)^[3]
f = map(S^1,module I,(vars S)^[3])
matrix f
///


submoduleByDegrees = method()
submoduleByDegrees(Module,ZZ):= (A,n)->(
     F := cover A;
     L := flatten degrees F;
     L1:= positions(L,d->d<=n);
     image (inducedMap(A,cover A)*F_L1)
     )

submatrixByDegrees = method()
submatrixByDegrees(Matrix, List, List) := (f,D,E)->(
     --D,E are lists of degrees for rows and cols, respectively
     Ltarget := flatten degrees target f;
     Lsource := flatten degrees source f;
     Lt:= toList select(toList(0..(rank target f)-1),i->member(Ltarget_i, D));
     Ls:= toList select(toList(0..(rank source f)-1),i->member(Lsource_i, E));
     map(target((target f)^Lt),source((source f)_Ls), f_Ls^Lt)
     )

TateResolution = method()
TateResolution(Module,ZZ,ZZ) := (M,lower,upper) ->(
    d := transpose (res(M, LengthLimit => upper)).dd_upper;
    betti res (coker d, LengthLimit =>upper+lower)
    )
TateResolution(Module,ZZ) := (M,b) -> TateResolution(M,b,b)
TateResolution(Module) := M-> TateResolution(M,5,5)

-----------------------------
--------Tests-----------
--------------------------------
TEST ///
S = kk[a,b,c]
M = S^1/intersect(ideal"a,b", ideal"b,c",ideal"c,a")
hf(5..5,coker S2(-5,M))
betti prune S2(-5,M)
///

TEST///
kk= ZZ/101
S = kk[x,y,z]
F = matrix"x3,y3"
R = S/ideal F;
high = 10

MM = matrix"x2, yz"
M = coker MM;     
G = res(M, LengthLimit =>high)
r = isSurjCIOperator(F,G)
low = r-2
E = decomposeResolution(F,G,low,10);
assert(betti E == betti truncate(low,G))

MM =  random(R^{0,-1}, R^{-2,-4,-5});
M = coker MM;     
G = res(M, LengthLimit =>high)
r = isSurjCIOperator(F,G)
low = r-2
E = decomposeResolution(F,G,low,10);
assert(betti E == betti truncate(low,G))
///


TEST///
kk= ZZ/101
S = kk[x,y,z]
t = random(S^{2:-1,2:-2}, S^{3:-1,4:-2})
ss = splittings(syz t, t)
ss/betti


(A,B) = (syz t, t)
(sigma, tau)= splittings(A,B)
     assert(A*sigma+tau*B == id_(source B));
     assert(sigma*tau==0);
     assert(B*tau == id_(target B));
     assert(sigma*A == id_(source A));

(a,b) = (transpose ss_0, transpose ss_1)
(sigma, tau)=splittings(a,b)
     assert(a*sigma+tau*b == id_(source b));
     assert(sigma*tau==0);
     assert(b*tau == id_(target b));
     assert(sigma*a == id_(source a));

///


///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
///

------------
--special purpose code
--

----- look for small examples
--This code searches for pairs of monomials of degree d
-- in the given ring (mod the c d-th powers of the variables) 
--of complexity c (that is,
--dim Ext(R/(m1, m2),k)=c), and tallies the sequence of B ranks
--for a high syzygy of R/(m1,m2).

--Conclusion: in every one of these cases, the sequences
--{rank target B(i)} and {rank source B(i)} are *strictly increasing
--for i = 2..4 (and weakly increasing between i = 1,2.)
--also, the multiplicity is always 8, 12 or 17.
twoMonomials = method(Options => {Optimism => 0})
twoMonomials(ZZ,ZZ) := opts-> (c,d)->(
Blist := null;
M0:=null;
MF:=null;
B:= null;
x := symbol x;
S := ZZ/101[x_0..x_(c-1)];
f := map(S^1, S^{c: -d}, (i,j) -> x_j^d);
ff := f*random(source f, source f);
R := S/ideal f;
L := flatten entries basis R;
for e from 2 to c*(d-1) do(
L1 := select(L, m -> (degree m)_0 == e);
--make all pairs
pL1 :=(unique flatten apply(L1, i-> apply(L1, j-> set(i,j))))/toList;
time Blist = apply(pL1, m -> (
	M0 = R^1/ideal m;
	--<< m << endl;
    	MF = matrixFactorization(ff, highSyzygy(opts, M0));
	B = Branks MF;
	scan(c-1, j-> (
		if last B_(j+1)-last(B_j)<0 then(
		print m;
		error();
		)));
	if B_0 != {0,0} then
	{B,toList m}
	else null
	)
    );
Blist = select(Blist, i-> i=!=null);
<< e <<endl;
<< tally(Blist/(k->k_0))<<endl;<<endl;
<<flush
)
)


--sumtwoMonomials(c,d)
--tallies the sequences of B-ranks that occur for sums of pairs of 
--monomials in R = S/(d-th powers of the variables), with
--full complexity (=c); that is,
--for an appropriate syzygy M of 
--M0 = R/(two monomials of the same degree)
sumTwoMonomials = method()
sumTwoMonomials(ZZ,ZZ) := (c,d) ->(
Blist := null;
M0:=null;
MF:=null;
B:= null;
x := symbol x;
S := ZZ/32003[x_0..x_(c-1)];
f := map(S^1, S^{c: -d}, (i,j) -> x_j^d);
ff := f*random(source f, source f);
R := S/ideal f;
L := flatten entries basis R;
for e from 2 to c*(d-1) do(
--make all pairs
L1 := select(L, m -> (degree m)_0 == e);
pL1 :=(unique flatten apply(L1, i-> apply(L1, j-> set(i,j))))/toList;
ppL1 := select(pL1, j->#j == 2);
time Blist = apply(ppL1, m -> (
	M0 = R^1/ideal(m_0+m_1);	
	--<< m << endl;
    	MF = matrixFactorization(ff, highSyzygy M0);
	B = Branks MF;
	scan(c-1, j-> (
		if last B_(j+1)-last(B_j)<0 then(
		print m;
		error("example of decreasing source ranks");
		)));
	if B_0 != {0,0} then
	{B,toList m}
	else null
	)
    );

Blist = select(Blist, i-> i=!=null);
<< e <<endl;
<< tally(Blist/(k->k_0))<<endl;<<endl;
)
)

--moduleAsExt = method()
--moduleAsExt(Module,Ring) := (MM,R) ->()

moduleAsExt = method()
moduleAsExt(Module,Ring) := (MM,R) ->(
    Ops := ring MM;
    reg := regularity MM;
    MMr := truncate(reg, MM);
    F := res MMr;
    K := res(coker vars R, LengthLimit => reg+numgens R);
    K2 := res(coker K.dd_3, LengthLimit=>5);
    T := makeT(presentation R, K, 2);
    Tmat := T_0;
    scan(drop(T,1), t->Tmat = Tmat||t);
    --Two subroutines
    insertT := phi -> (
	--replace each entry of phi by the 
	--appropriate linear combination of the rows of Tmat.
	--Note that the entries of phi must be linear forms of Ops
	--and the output is a matrix of scalars over thing ring R.
	v := vars ring phi;
	L := entries phi; -- list of lists of lin forms in Ops
        matrix apply(#L, i -> 
	    apply(#L_i, 
		j-> sub(diff(v, L_i_j),R)*Tmat))
	);
    dsum := (p,F)-> directSum apply(p, i->F);
    --End subroutines
    phi := F.dd_1;
    
    print betti (Ks := dsum(rank source phi, K));
    print betti (Kt := dsum(rank target phi,R^{2}**K2));
    phiT := map(Ks_0,Kt_0,insertT phi);
    print betti phiT;
    
    error();
    extend(dsum(rank source phi, K), 
	dsum(rank target phi,R^{2}**K2), 
	phiT)    
        )


///
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
  kk = ZZ/101;
  S = kk[a,b,c];
  ff = matrix{{a^2, b^2}};
  R = S/ideal ff;
  Ops = kk[x_1,x_2]
  MM = Ops^1/ideal(x_1^2*x_2)  
  moduleAsExt(MM,R)
  ///
-----------------------------
--------Documentation-----------
--------------------------------
--docTemplate

doc ///
Key
 moduleAsExt
 (moduleAsExt, Module, Ring)
Headline
 Find a module with given assymptotic resolution
Usage
 M = moduleAsExt(MM,R)
Inputs
 MM:Module
  module over poly ring with c variables of degree 2
 R:Ring
  (graded) complete intersection ring of codim c, edim n
Outputs
 M:Module
  module over R such that Ext_R(M,k) = M\otimes \wedge(k^n)
Description
 Text
  Suppose that $R = k[a_1,\dots, a_n]/(f_1,\dots,f_c)$ and
  $F = k[x_1,\dots,x_c]\otimes \wedge k^n$, so that the minimal
  $R$-free resolution of $k$ has underlying module $R\otimes F^*$.
  
  We truncate MM at its regularity and shift so it is generated
  in degree 0, then pass to the ring
  $E = Ext_R(k,k)$, and set  
  $N := E^{n}\otimes trunc(n,E\otimes MM).$ We then resolve
  $N$ over $E$.
 Example
  kk = ZZ/101;
  S = kk[a,b,c];
  ff = matrix{{a^4, b^4}};
  R = S/ideal ff;
  Ops = kk[x_1,x_2]
  MM = Ops^1/ideal(x_1^2*x_2)  
  betti presentation prune moduleAsExt(MM,R)  
       ///

{*
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
--uninstallPackage("CompleteIntersectionResolutions")
installPackage("CompleteIntersectionResolutions")
viewHelp moduleAsExt
*}


doc///
Key
  CompleteIntersectionResolutions
Headline 
  "Resolution over a Complete Intersection"
Description 
 Text
  The resolution of a module over a hypersurface ring 
  (graded or local) is always periodic of period at most 2 (Eisenbud **** ),
  but the structure of minimal resolutions over a 
  complete intersection is a topic of active research. 
  This package contains 
  code that helps analyze (graded) examples. 
  
  In particular, we construct
  the higher matrix factorization of Eisenbud-Peeva. (The construction requires
  a `general' set of generators for the ideal of the complete intersection. Unless
  the complete intersection is homogeneous and generated by elements of a single degree,
  it may not be possible to choose this homogeneously, even when
  the ideal of the complete intersection is homogeneous.)
  
  Here are some suggestive examples of matrix factorizations
 Example
  c = 2
  S = ZZ/101[x_1..x_c, a_(1,1)..a_(c,c)];
  X = matrix{{x_1..x_c}}
  ff = X*genericMatrix(S,a_(1,1),c,c)
  R = S/ideal ff;
  F = res(coker (R**X) , LengthLimit =>c+1)
  M = coker F.dd_(c+1)
  MF = matrixFactorization(ff,M)
  netList Branks MF
  netList Bmats MF

  c = 3
  S = ZZ/101[x_1..x_c, a_(1,1)..a_(c,c)];
  X = matrix{{x_1..x_c}}
  ff = X*genericMatrix(S,a_(1,1),c,c)
  R = S/ideal ff;
  F = res(coker (R**X) , LengthLimit =>c+1)
  M = coker F.dd_(c+1)
  MF = matrixFactorization(ff,M)
  netList Branks MF
  netList Bmats MF
 Text
  The ranks of the stack of matrices that are used 
  in the construction of the matrix factorization, and the matrices
  themselves,
  are obtained from Branks MF and Bmats MF.

 Text
  The package also contains routines for decomposing resolutions
 Example
  S = ZZ/101[x,y,z];
  F = map(S^1, S^2, matrix"x2, z3");
  f1 = x^2;
  f2 = y^3;
  R = S/ideal F;
  M = R^1/ideal gens R;
  G1 = res(M,LengthLimit => 5);
  N = coker transpose G1.dd_5;
  G = res(N,LengthLimit => 11)
 Text
  In fact, a truncation of the resolution is an extension of a periodic resolution
  that is the kernel of the ci operator associated to F_0.
  For instance, the 3x5 matrix that is the first differential of E 
  reappears as the lower right 3x5 block of the third and fifth matrix, and the 
  5x7 matrix defining the second differential reappears as the lower
  right 5x7 block of the 4th matrix in the example below.
 Example
  r = isSurjCIOperator(F,G)
  E = decomposeResolution(F, G, r-2, 11);
  betti G
  betti E
  L=E.dd
///



{*
restart
uninstallPackage("CompleteIntersectionResolutions")
installPackage("CompleteIntersectionResolutions")
loadPackage("CompleteIntersectionResolutions", Reload=>true)
*}



{*
restart
uninstallPackage("CompleteIntersectionResolutions")
installPackage("CompleteIntersectionResolutions")
*}



doc ///
   Key 
    Optimism
   Headline
    Option to highSyzygy
   Usage
    highSyzygy(M, Optimism => 1)
   Inputs
    Optimism:ZZ
   Description
    Text
     If highSyzygy(M) chooses the p-th syzygy,
     then highSyzygy(M,Optimism=>r) chooses the (p-r)-th syzygy.
     (Positive Optimism chooses a lower "high" syzygy, negative
     Optimism a higher "high" syzygy.
    Example
   Caveat
    Are there cases when positive Optimism is justified?
   SeeAlso
    mfBound
    highSyzygy
///



doc ///
   Key 
    Check
   Headline
    Option for matrixFactorization
   Usage
    matrixFactorization(ff,m,Check => true)
   Inputs
    Check:Boolean
   Description
    Text
     Makes matrixFactorization perform various checks as it computes.
   SeeAlso
    matrixFactorization
 ///



doc ///
   Key 
    highSyzygy
    (highSyzygy, Module)
   Headline
    Returns a syzygy module one beyond the regularity of Ext(M,k)
   Usage
    M = highSyzygy M0
   Inputs
    M0:Module
     over a complete intersection ring
   Outputs
    M:Module
     a syzygy module of M0
   Description
    Text
     A "high syzygy" over a complete intersection is one
     such that general ci-operators have split kernels
     when applied recursively on cosyzygy chains of 
     previous kernels.
     
     ASSUMING our
     conjecture that Ext surjects onto its S2-ification, this
     should be the first syzygy beyond the regularity of
     the even and odd Ext modules Ext(M,k). This position is
     computed by the script mfBound.
     
     If p = mfBound M0, then highSyzygy M0
     returns the p-th syzygy of M0.
     (if F is a resolution of M this is the cokernel 
     of F.dd_p). Optimism => r as optional
     argument, highSyzygy(M0,Optimism=>r)
     returns the (p-r)-th syzygy. The script is
     useful with matrixFactorization(ff, highSyzygy M0).
    Example
     S = ZZ/101[x,y,z]
     f = matrix"x3,y3+x3,z3+x3+y3"
     ff = f*random(source f, source f)
     R = S/ideal f
     M0 = R^1/ideal"x2z2,xyz"
     betti res (M0, LengthLimit => 7)
     mfBound M0
     M = betti res highSyzygy M0
     netList Branks matrixFactorization(ff, highSyzygy M0)
    Text
     In this case as in all others we have examined, 
     greater "Optimism" is not 
     justified:
    Example
     matrixFactorization(ff, highSyzygy(M0, Optimism=>1));
   Caveat
    A bug in the total Ext script means that the oddExtModule
    is sometimes zero, and this can cause a wrong value to be
    returned. 
   SeeAlso
    evenExtModule
    oddExtModule
    mfBound
    matrixFactorization
///




doc ///
   Key
    mfBound
    (mfBound, Module)
   Headline
    determines how high a syzygy to take for "matrixFactorization"
   Usage
    p = mfBound M
   Inputs
    M:Module
     over a complete intersection
   Outputs
    p:ZZ
   Description
    Text
     If p = mfBound M, then the p-th syzygy of M,
     which is computed by highSyzygy(M), 
     should (this is a conjecture) 
     be a "high Syzygy" in the sense required
     for matrixFactorization. In examples, the estimate
     seems sharp (except when M is already a high syzygy).
    
     The actual formula used is:
    
     mfBound M = 1+max(2*r_{even}, 1+2*r_{odd})
    
     where r_{even} = regularity evenExtModule M and
     r_{odd} = regularity oddExtModule M. Here
     evenExtModule M is the even degree part of
     Ext(M, (residue class field)).
   SeeAlso
    highSyzygy
    evenExtModule
    oddExtModule
    matrixFactorization
///



doc ///
   Key
    ExtModuleData
    (ExtModuleData, Module)
   Headline
    Even and odd Ext modules and their regularity
   Usage
    L = ExtModuleData M
   Inputs
    M:Module
     Module over a complete intersection S
   Outputs
    L:List
     L = \{evenExtModule, oddExtModule, reg0, reg1\}
   Description
    Text
     Suppose that M is a module over a complete intersection R
     so that 
     
     E := ExtModule M 
     
     is a module generated in degrees >=0 
     over a polynomial ring T' 
     generated in degree 2, and
     
     E0 := evenExtModule M and 
     E1 := oddExtModule M
     
     are modules generated in degree >= 0
     over a polynomial ring T with generators 
     in degree 1.
     
     The script returns 
     
     L = \{E0,E1, regularity E0, regularity E1\}
     
     and prints a message if |reg0-reg1|>1.
     
     If we set r = max(2*reg0, 1+2*reg1),
     and F is a resolution of M, then 
     coker F.dd_{(r+1)}
     is the first szygy module of M such that
     regularity evenExtModule M =0 AND
     regularity oddExtModule M =0 
     
     We have been using regularity ExtModule M 
     as a substitute for r,
     but that's not always the same.
    Example
     S = ZZ/101[a,b,c,d];
     f = map(S^1, S^4, (i,j) -> S_j^3)
     R = S/ideal f;
     M = R^1/ideal"ab2+cd2";     
     betti (F = res(M, LengthLimit => 5))
     E = ExtModuleData M;
     E_2     
     E_3          
     r = max(2*E_2,2*E_3+1)
     Er = ExtModuleData coker F.dd_r;
     regularity Er_0
     regularity Er_1
     regularity evenExtModule(coker F.dd_(r-1))
     ff = f*random(source f, source f);
     matrixFactorization(ff, coker F.dd_(r+1));
    Text
     This succeeds, but we would get an error from
     
     matrixFactorization(ff, coker F.dd_r)
     
     because one of the CI operators would not be surjective.
   Caveat
     ExtModule creates a ring inside the script, so if it's run
     twice you get modules over different rings. This should be
     changed.
   SeeAlso
    ExtModule
    evenExtModule
    oddExtModule
///

doc ///
   Key
    submatrixByDegrees
    (submatrixByDegrees, Matrix, List, List)
   Headline
    submatrix of elements with given row and col degrees
   Usage
    m1 = submatrixByDegrees(m,rowDegList,colDegList)
   Inputs
    m:Matrix
      map between graded FREE modules
    rowDegList:List
      list of integers, desired row (target) degrees
    colDegList:List
      list of integers, desired column (source) degrees
   Outputs
    m1:Matrix
      submatrix of m
   Description
    Text
    Example
     S = ZZ/2[a,b,c,d];
     m = random(S^{2,4,6},S^{ -1,3});
     betti m
     m1 = submatrixByDegrees(m,{3},{4});
     betti m1
     m1 = submatrixByDegrees(m,{ -2,-4},{1});
     betti m1
///


document{Key =>  hf,
     Headline => "Hilbert function in a range",
     Usage => "using hilbertFunction(ZZ,Module),
     hf returns a Sequence or List
     of the values of the Hilbert function of the Module
     at the integer arguments specified by the Sequence or List."}

doc ///
   Key
    splitResolution
    (splitResolution,Matrix,ChainComplex,List)
    (splitResolution,Matrix,ChainComplex,ZZ,ZZ)    
   Headline
    Split a resolution as ker and image of first CI operator    
   Usage
    F1 = splitResolution(ff,F,L)
    F1 = splitResolution(ff,F,low,high)    
   Inputs
    ff:Matrix
       typically a regular sequence in a ring S
    F:ChainComplex 
      over S/ideal ff
    L:List
      range of indices of F
    low:ZZ
    high:ZZ
      alternative way to specify the range L
   Outputs
    F1:ChainComplex
      F written in terms of a basis adapted to first CI operator
   Description
    Text
     L =toList(low..high)
     is a list of integers corresponding 
     to consecutive spots in the resolution F over a complete
     intersection R = S/ideal ff, where ff = matrix{{f0..fn}}.
     Assumes that the operators
     t_i: F_i --> F_(i-2)
     corresponding to f0 are
     surjective for all i in L.
     Computes s_i = ker t_i and splittings
     sigma_i: F_i --> source s_i
     tau_i : cover image t_i --> F_i
     returns the list of quadruples
     apply(L, i->
	  {s_i, sigma_i, tau_i,t_i}
	  )
     These maps implement 
     a decomposition of F, in the sense that:
     s_i = ker t_i, 
     sigma_i*s_i = 1, 
     t_i*tau_i = 1 (on F_(i-1) twisted by the degree of f0)     
     s_i*sigma_i + tau_i*t_i = 1_(F_i)
     sigma_i * tau_i = 0
    Example
     S = ZZ/101[x,y]
     ff = matrix"x2y, x3+y3"
     f1 = (flatten entries ff)_0
     R = S/ideal ff
     kkk=coker vars R
     F = res(kkk, LengthLimit => 10)
     decomposeResolution(ff, F, 3,7)
     splitResolution(ff, F, {3,4,5,6,7})
   SeeAlso
    decomposeResolution
///

doc ///
   Key
    isLinear
    (isLinear, Matrix)
   Headline
    check whether matrix entries have degree 1
   Usage
    b = isLinear M
   Inputs
    M:Matrix
   Outputs
    b:Boolean
   Description
    Text
     Note that a linear matrix, in this sense, can still
     have different target degrees (in which case the
     cokernel decomposes into a direct sum by generator
     degree.)
///

doc ///
   Key
    TateResolution
    (TateResolution, Module, ZZ,ZZ)
    (TateResolution, Module, ZZ)
    (TateResolution, Module)
   Headline
    TateResolution of a module over an exterior algebra
   Usage
    F = TateResolution(M,lower,upper)
   Inputs
    M:Module
    lower:ZZ
    upper:ZZ
          lower and upper bounds for the resolution
   Outputs
    F:ChainComplex
   Description
    Text
     Forms an interval, lower..upper, 
     of a doubly infinite free resolution of 
     a a Cohen-Macaulay
     module over a Gorenstein ring, such as
     any module over an exterior algebra (actually,
     any module over any ring.)
    Example
     E = ZZ/101[a,b,c, SkewCommutative=>true]
     M = coker map(E^2, E^{-1}, matrix"ab;bc")
     presentation M
     TateResolution(M,2,7) 
///

doc ///
   Key
    makeT
    (makeT,Matrix, ChainComplex,ZZ)
    (makeT,Matrix, ChainComplex,Matrix, ZZ)    
   Headline
    make the CI operators on a complex
   Usage
    T = makeT(ff,F,i)
    T = makeT(ff,F,t0,i)
   Inputs
    ff:Matrix
      1xc matrix whose entries are a complete intersection in S
    F:ChainComplex
      over S/ideal ff
    t0:Matrix
      CI-operator on F for ff_0 to be preserved
    i:ZZ
      define CI operators from F_i \to F_{i-2}
   Outputs
    L:List
      of CI operators F_i \to F_{i-2} corresponding to entries of ff
   Description
    Text
     substitute matrices of two differentials of F into S = ring ff,
     compose them, and divide by entries of ff, in order.
     If the second Matrix argument t0 is present, use it
     as the first CI operator. 
     
     The degrees of the targets of the T_j are
     changed by the degrees of the f_j to make the T_j
     homogeneneous.
    Example
     S = ZZ/101[x,y,z];
     ff = matrix"x3,y3,z3";
     R = S/ideal ff;
     M = coker matrix"x,y,z;y,z,x";
     betti (F = res M)
     T = makeT(ff,F,3);
     netList T
     isHomogeneous T_2
   Caveat
    Script assumes that ring F == (ring ff)/(ideal ff).
    It might be more useful to return the operators as matrices
    over S rather than over R, since this is what we'd need
    for things like matrixFactorization (where this process
    currently done on the fly, not calling makeT)
///

doc///
Key
 isSurjCIOperator
 (isSurjCIOperator, Matrix, ChainComplex)
 (isSurjCIOperator, Matrix, ChainComplex, ZZ) 
Headline
 Checks whether a CI operator is surjective
Usage
 i = isSurjCIOperator(ff,F)
Inputs
 ff:Matrix
    1xc matrix containing a regular sequence
 FF:ChainComplex 
    over S/ideal ff
Outputs
  i:ZZ
    point from which CI operator corresponding to ff_0 is surjective.
///

doc ///
Key
 decomposeResolution
 (decomposeResolution, Matrix, ChainComplex, ZZ,ZZ)
Headline 
 decomposes a resolution over a complete intersection
Usage
 E = decomposeResolution(ff,G,low,high)
Inputs
 ff:Matrix
   a row consisting of a regular sequence
 G:ChainComplex
   a resolution over (ring ff)/(ideal ff)
 low:ZZ
 high:ZZ
   the ci operators starting from G_{low}...G_{high} corresponding to ff_0 should be surjective
Outputs
 E:ChainComplex
   a copy of G, but with the maps written as four blocks corresponding to the natural splittings
Description
 Text
  ff=matrix{{f0..fn}} is a matrix of a regular sequence in a poly ring S.
  G is a resolution over R:=S/ideal ff.
  G_{lower} and G_{upper} are modules in the resolution G such that
  f_0 defines a surjective
  ci-operator t_i: G_i > G_{(i-2)} for each i = low+2..high.
  (Really this is the CI operator defined by f1..fn.)
  (thus low must be at least isSurjCIOperator(ff,G) -2.)

  The script computes
  s_i: ker t_i > G_i 
  and chooses splittings
  sigma_i: G_i > ker t_i

  Setting K_i = source s_i = ker t_i,
  we thus have G_i \cong K_i ++ K_{(i-2)} ++...
  The script returns a copy E of the complex G
  written in terms of this splitting,
  so that the map K_{(i-2j)} > K_{(i-1-2m)} induced by G.dd_i
  is (E.dd_i)^{[j]}_{[m]}. In particular, the map t:G_i>G_{(i-2)}
  becomes
  (E.dd_i)^{[1,2,..]}
     
  The components of E_i are numbered 0..(i-low)//2
  The sum of the first i components 
  is the kernel of the i-th iteration of t
  (where the t_{low} and t_{(low+1)} are replaced by 0).


 Example
  S = ZZ/101[x,y,z];
  ff = map(S^1, S^2, matrix"x2, z3");
  R = S/ideal ff;
  M = R^1/ideal gens R;
  betti (G1 = res(M,LengthLimit => 5));
  N = coker transpose G1.dd_5;
  betti (G = res(N,LengthLimit => 15))
 Text
  In fact, the resolution is an extension of a "true" codim 2 resolution by a "periodic part"
 Example
  r = isSurjCIOperator(ff,G)
  E = decomposeResolution(ff, G, 6, 9);
  betti E
  L=E.dd
///

doc ///
        Key 
	 ExtModule
	 (ExtModule, Module)
        Headline 
	 Ext^*(M,k) over a complete intersection as module over CI operator ring
        Usage
	 E = ExtModule M
        Inputs
	 M:Module
	   over a complete intersection ring
        Outputs
	 E:Module
	   over a polynomial ring with gens in even degree
        Description

         Text
	  Uses code of Avramov-Grayson described in Macaulay2 book
         Example
	  kk= ZZ/101
	  S = kk[x,y,z]
	  I1 = ideal "x3y"
	  R1 = S/I1
	  M1 = R1^1/ideal(x^2)
	  betti res (M1, LengthLimit =>5)
	  E = ExtModule M1
	  apply(toList(0..10), i->hilbertFunction(i, E))
	  Eeven = evenExtModule(M1)
	  apply(toList(0..5), i->hilbertFunction(i, Eeven))
	  Eodd = oddExtModule(M1)
	  apply(toList(0..5), i->hilbertFunction(i, Eodd))
	  --
	  use S
	  I2 = ideal"x3,yz"
	  R2 = S/I2
	  M2 = R2^1/ideal"x2,y,z"
	  betti res (M2, LengthLimit =>10)	  
	  E = ExtModule M2
	  apply(toList(0..10), i->hilbertFunction(i, E))
	  Eeven = evenExtModule M2
	  apply(toList(0..5), i->hilbertFunction(i, Eeven))
	  Eodd = oddExtModule M2
	  apply(toList(0..5), i->hilbertFunction(i, Eodd))
        SeeAlso 
	  evenExtModule 
	  oddExtModule
///
doc ///
        Key 
	 evenExtModule
	 (evenExtModule, Module)
        Headline 
	 even part of Ext^*(M,k) over a complete intersection as module over CI operator ring
        Usage
	 E = evenExtModule M
        Inputs
	 M:Module
	   over a complete intersection ring
        Outputs
	 E:Module
	   over a polynomial ring with gens in degree 1
        Description
         Text
	  Extracts the even degree part from ExtModule M
         Example
	  kk= ZZ/101
	  S = kk[x,y,z]
	  I2 = ideal"x3,yz"
	  R2 = S/I2
	  M2 = R2^1/ideal"x2,y,z"
	  betti res (M2, LengthLimit =>10)	  
	  E = ExtModule M2
	  apply(toList(0..10), i->hilbertFunction(i, E))
	  Eeven = evenExtModule M2
	  apply(toList(0..5), i->hilbertFunction(i, Eeven))
        SeeAlso 
	  ExtModule 
	  oddExtModule

     ///
doc ///
        Key 
	 oddExtModule
	 (oddExtModule, Module)
        Headline 
	 odd part of Ext^*(M,k) over a complete intersection as module over CI operator ring
        Usage
	 E = oddExtModule M
        Inputs
	 M:Module
	   over a complete intersection ring
        Outputs
	 E:Module
	   over a polynomial ring with gens in degree 1
        Description
         Text
	  Extracts the odd degree part from ExtModule M
         Example
	  kk= ZZ/101
	  S = kk[x,y,z]
	  I2 = ideal"x3,yz"
	  R2 = S/I2
	  M2 = R2^1/ideal"x2,y,z"
	  betti res (M2, LengthLimit =>10)	  
	  E = ExtModule M2
	  apply(toList(0..10), i->hilbertFunction(i, E))
	  Eodd = oddExtModule M2
	  apply(toList(0..5), i->hilbertFunction(i, Eodd))
        SeeAlso 
	  ExtModule 
	  evenExtModule
     ///


doc ///
Key
 makeHomotopies
 (makeHomotopies,Matrix,ChainComplex,ZZ)
 (makeHomotopies,Matrix,ChainComplex)
Headline
 returns a system of higher homotopies
Usage
 H = makeHomotopies(f,F,d)
Inputs
 f:Matrix
   1xn matrix of elements of S
 F:ChainComplex
   admitting homotopies for the entries of f
 d:ZZ
   how far back to compute the homotopies (defaults to length of F)
Outputs
 H:HashTable
   gives the higher homotopy from F_i corresponding to a monomial with exponent
   vector L as the value $H#\{L,i\}$
Description
 Text
  Given a $1\times n$ matrix f, and a chain complex F,
  the script attempts to make a family of higher homotopies
  on F for the elements of f, in the sense described, for
  example, in Eisenbud "Enriched Free Resolutions and Change
  of Rings".
  
  The output is a hash table with entries of the form $\{J,i\}=>s$, 
  where
  J is a list of non-negative integers, of length n
  and $H\#\{J,i\}: F_i->F_{i+2|J|-1}$ are maps satisfying 
  the conditions
  $$
  H\#\{e0,i\} = d;
  $$
  and
  $$
  H#\{e0,i+1\}*H#\{e,i\}+H#\{e,i-1\}H#\{e0,i\} = f_i,
  $$ 
  where $e0 = \{0,\dots,0\}$ and $e$ is the index of degree 1
  with a 1 in the $i$-th place;
  and, for each index list I with |I|<=d,
  $$
  sum_{J<I} H#\{I\setminus J, \} H#\{J, \} = 0.
  $$
 Example
  kk=ZZ/101
  S = kk[a,b,c,d]
  F = res ideal vars S  
  f = matrix{{a,b,c}}
  homot = makeHomotopies(f,F,2)
 Text
  In this case the higher homotopies are 0:
 Example
  L = sort select(keys homot, k->(homot#k!=0 and sum(k_0)>1))
 Text
  On the other hand, if
  we take a complete intersection and something
  contained in it in a more complicated situation,
  the program gives nonzero higher homotopies:
 Example
  kk= ZZ/32003;
  S = kk[a,b,c,d];
  M = S^1/(ideal"a2,b2,c2,d2");
  F = res M
  f = random(S^1,S^{2:-5});
  homot = makeHomotopies(f,F,5)
 Text
  We can see that all 6 potential higher homotopies are nontrivial:
 Example
  L = sort select(keys homot, k->(homot#k!=0 and sum(k_0)>1))
  #L
  netList L
 Text
  For example we have:
 Example
  homot#(L_0)
 Text
  But all the homotopies are minimal in this case:
 Example
  k1 = S^1/(ideal vars S);
  select(keys homot,k->(k1**homot#k)!=0)
SeeAlso
 makeHomotopies1
///


doc ///
Key
 makeHomotopies1
 (makeHomotopies1, Matrix,ChainComplex,ZZ)
 (makeHomotopies1, Matrix,ChainComplex) 
Headline
 returns a system of first homotopies
Usage
 H = makeHomotopies1(f,F,d)
Inputs
 f:Matrix
   1xn matrix of elements of S
 F:ChainComplex
   admitting homotopies for the entries of f
 d:ZZ
   how far back to compute the homotopies (defaults to length of F)
Outputs
 H:HashTable
   gives the homotopy from F_i corresponding to f_j
   as the value $H#\{j,i\}$
Description
 Text
   Same as makeHomotopies, but only computes the ordinary 
   homotopies, not the higher ones. Used in exteriorTorModule
SeeAlso
 makeHomotopies
 exteriorTorModule
///

doc ///
Key
 makeModule
 (makeModule, Ring,List,HashTable)
Headline
 realize a free module with (anti)-commuting operators as a module
Usage
 M =  makeModule(R,T,Hk)
     --T is a list of free modules F_i over over
     --k =  coefficientRing R.
     --H is a HashTable with pairs of the form {j,i} => phi,
     --where phi: F_i\to F_(i+1).
     --The script takes R**\sum F_i as a graded R-module, 
     --where the j-th generator of R acts as H#{j,i}.

Inputs
 R:Ring
  The ring over which the module will be defined
 T:List
  A List of free modules over the coefficient ring of R, the components of the new module
 Hk:HashTable
  The value Hk#{j,i} specifies the action of the j-th variable
  as a map T_i --> T_(i+1)
Outputs
 M:Module 
  Module over R (not a minimal presentation
Description
 Text
  Used in exteriorTorModule
SeeAlso
 exteriorTorModule
///

doc ///
Key
 S2
 (S2,ZZ,Module)
Headline
 Universal map to a module satisfying Serre's condition S2
Usage
 f = S2(b,M)
Inputs
 b:ZZ
   degree bound to which to carry the computation
 M:Module
Outputs
 f:Matrix
   defining a map M-->M' that agrees with the
   S2-ification of M in degrees $\geq b$
Description
 Text
  If M is a graded module over a ring S, then the S2-ification
  of M is \sum_{d \in ZZ} H^0((sheaf M)(d)), which may be computed
  as lim_{d->\infty} Hom(S/I_d,M), where I_d is any sequence
  of ideals contained in higher and higher powers of S_+.
  There is a natural restriction map 
  f: M = Hom(S,M) \to Hom(I_d,M).
  We compute all this using the ideals 
  I_d generated by the d-th powers
  of the variables in S.
  
  Since the result may not be finitely generated (this happens
  if and only if M has an associated prime of dimension 1), we
  compute only up to a specified degree bound b. For the result to
  be correct down to degree b, it is sufficient to compute
  Hom(I,M)
  where I \subset (S_+)^{r-b}.
 Example
  kk=ZZ/101
  S = kk[a,b,c,d]
  M = truncate(3,S^1)
  betti S2(0,M)
  betti S2(1,M)
  M = S^1/intersect(ideal"a,b,c", ideal"b,c,d",ideal"c,d,a",ideal"d,a,b")
  prune source S2(0,M)
  prune target S2(0,M)
SeeAlso
  "IntegralClosure"
  "makeS2"
  "BGG"
  "cohomology"
  "HH^ZZ SumOfTwists"
Caveat
 Text
  S2-ification is related to computing cohomology and to 
  computing integral closure; there are scripts in
  those packages that produce an S2-ification, but one takes
  a ring as argument and the other doesn't produce the 
  comparison map.
///

doc///
Key
  splittings
  (splittings, Matrix, Matrix)
Headline
  a sample documentation node
Usage
  x = splittings(a,b)
Inputs
  a:Matrix
    maps into the kernel of b
  b:Matrix
    representing a surjection from target a to a free module
Outputs
  L:List
    L = \{sigma,tau\}, splittings of a,b respectively
Description
 Text
     Assuming that (a,b) are the maps of a right exact
     sequence 
     
     $0\to A\to B\to C \to 0$
     
     with B, C free,
     the script produces a pair of maps sigma, tau
     with $tau: C \to B$ a splitting of b and
     $sigma: B \to A$ a splitting of a; that is,
     
     $a*sigma+tau*b = 1_B$
     
     $sigma*a = 1_A$
     
     $b*tau = 1_C$
 Example
   kk= ZZ/101
   S = kk[x,y,z]
   t = random(S^{2:-1,2:-2}, S^{3:-1,4:-2})
   ss = splittings(syz t, t)
   ss/betti
///

     doc ///
        Key 
	 toArray
	 (toArray, List)
	 (toArray, ZZ)
        Headline
	 makes an array from a List or from a single integer
	Usage
	 arr = toArray L
	 arr = toArray n
	Inputs
	 L:List
	 n:ZZ
	Outputs
	 arr:Array
     ///
     
doc ///
Key
 matrixFactorization
 (matrixFactorization, Matrix, Module)
Headline
 Maps in a higher codimension matrix factorization
Usage
 MF = matrixFactorization(ff,M)
Inputs
 ff:Matrix
   a sufficiently general regular sequence in a ring S
 M:Module
   a high syzygy over S/ideal ff 
Outputs
 MF:List
    \{d,h\}, where d:A_1 \to A_0 and h is a hashTable of ``partial homotopies''
Description
 Text
  The input module M should be a ``high syzygy'' over
  R = S/ideal ff.  In all example we
  know it suffices for Ext^{even}_R(M,k) and Ext^{odd}_R(M,k) to have negative regularity
  over the ring of CI operators (regraded with variables of degree 1).
  
  If the CI operator at some stage of the induction is NOT surjective,
  then the script returns a String containing the presentation matrix
  of M. This condition can be caught by testing whether the
  returned value is a String or a List.
  
  When the optional input Check==true (the default), 
  the properties in the definition of Matrix Factorization are verified

  If the CI operators at each stage are surjective (that is, if
  M is really a high syzygy), then:
  
  The output is a list   
  \{d,h\}. 
  
  The map d is a special lifting to S of a presentation of
  M over R. To explain the contents, we introduce some notation
  (from our paper ****):

  R(i) = S/(ff_0,..,ff_{i-1}). Here 0<= i <= c, and R = R(c)
  and S = R(0).
  
  B(i) = the matrix (over S) representing d_i: B_1(i) \to B_0(i)
  
  d(i): A_1(i) \to A_0(i) the restriction of d = d(c).
  where A(i) = \oplus_{i=1}^p B(i)
  
  The object h is a hashTable. 
  The map h#p:target A(p) \to source A(p)
  is a homotopy for ff#p on the restriction
  d(p): over the ring R#(p-1) = S/(ff#1..ff#(p-1),
  so d(p) * h#p = ff#p mod (ff#1..ff#(p-1).
  
  In addition, h#p * d(p) induces ff#p on B1#p 
  mod (ff#1..ff#(p-1).
  
  Here is a simple codim 2 example:
 Example
  S = kk[a,b,u,v]
  ff = matrix"au,bv"
  R = S/ideal ff
  M0 = R^1/ideal"a,b"
  M = highSyzygy M0
  MF = matrixFactorization(ff,M);
  netList Branks MF
  netList Bmats MF
  betti res(M, LengthLimit => 7)
  infiniteBettiNumbers (MF,7)
  betti res pushForward(map(R,S),M)
  finiteBettiNumbers MF
SeeAlso
  finiteBettiNumbers
  infiniteBettiNumbers
  highSyzygy
  Bmats
  Branks
///

///
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp matrixFactorization
///

doc///
Key
 finiteBettiNumbers
 (finiteBettiNumbers, List)
Headline
 betti numbers of finite resolution computed from a matrix factorization
Usage
 L = finiteBettiNumbers MF
Inputs
 MF:List
   List of HashTables as computed by "matrixFactorization"
Outputs
 L:List
   List of betti numbers
Description
 Text
  Uses the ranks of the B matrices in a matrix factorization
  for a module M over S/(f_1,..,f_c) to compute the betti numbers
  of the minimal resolution of M over S, which is the sum
  of the Koszul complexes K(f_1..f_{j-1}) tensored with B(j)
 Example
  S = kk[a,b,u,v]
  ff = matrix"au,bv"
  R = S/ideal ff
  M0 = R^1/ideal"a,b"
  F = res(M0, LengthLimit =>3)
  M = coker F.dd_3;
  MF = matrixFactorization(ff,M);
  betti res pushForward(map(R,S),M)
  finiteBettiNumbers MF
  infiniteBettiNumbers(MF,5)
  betti res (M, LengthLimit => 5)
SeeAlso
  matrixFactorization
  infiniteBettiNumbers
///

doc ///
Key
 infiniteBettiNumbers
 (infiniteBettiNumbers, List, ZZ)
Headline
 betti numbers of finite resolution computed from a matrix factorization
Usage
 L = finiteBettiNumbers (MF,len)
Inputs
 MF:List
   List of HashTables as computed by "matrixFactorization"
 len:ZZ
   length of betti number sequence to produce
Outputs
 L:List
   List of betti numbers
Description
 Text
  Uses the ranks of the B matrices in a matrix factorization
  for a module M over S/(f_1,..,f_c) to compute the betti numbers
  of the minimal resolution of M over R, which is the sum
  of the divided power algebras on c-j+1 variables tensored with B(j).
 Example
  S = kk[a,b,u,v]
  ff = matrix"au,bv"
  R = S/ideal ff
  M0 = R^1/ideal"a,b"
  F = res(M0, LengthLimit =>3)
  M = coker F.dd_3;
  MF = matrixFactorization(ff,M);
  betti res pushForward(map(R,S),M)
  finiteBettiNumbers MF
  infiniteBettiNumbers(MF,5)
  betti res (M, LengthLimit => 5)
SeeAlso
  matrixFactorization
  finiteBettiNumbers
///

{*doc ///
Key
 BMaps
 (BMaps, List)
Headline
 The stack of "B" maps making up a matrix factorization
Usage
 L = BMaps MF
Inputs
 MF:List
   List of HashTables as computed by "matrixFactorization"
Outputs
 L:List
   List of matrices
Description
 Text
 Example
  S = kk[a,b,u,v]
  ff = matrix"au,bv"
  R = S/ideal ff
  M0 = R^1/ideal"a,b"
  F = res(M0, LengthLimit =>3)
  M = coker F.dd_3;
  MF = matrixFactorization(ff,M);
  BMaps MF
  netList ((BMaps MF)/betti)
SeeAlso
  matrixFactorization
  finiteBettiNumbers
  infiniteBettiNumbers
///
*}
doc///
Key
  exteriorTorModule
  (exteriorTorModule, Matrix, ChainComplex)
Headline
  Homology of a complex **k as a module over an exterior algebra
Usage
  T = exteriorTorModule(f,F)
Inputs
  f:Matrix
    1 x c, entries must be homotopic to 0 on F
  F:ChainComplex
    A minimal complex, typically a resolution of a module annihilated by ideal f
Outputs
  T:Module
    Module over an exterior algebra with variables corresponding to elements of f
Description
 Text
  Suppose that F is a minimal 
  complex over a ring S with residue field k, and that
  multiplication by the elements of f are null-homotopic on F.
  This script calls makeHomotopies1 to compute 
  homotopies for multiplication by the f_i on F.
  This makes F a homotopy associative, homotopy commutative graded module
  over the Koszul complex of f. Thus F**k is a module over \Lambda(k^{length f}).
  
  The script calls makeModule to compute a (non-minimal) presentation of this module.
  From the description by matrix factorizations we see that
  when M is a high syzygy and F is its resolution,
  then the presentation of Tor(M,S^1/mm) always has generators
  in degrees 0,1, corresponding to the targets and sources of the
  stack of maps B(i). We CONJECTURE that the relations are all in degrees 1,2,
  and that the resolution is componentwise linear in a suitable sense.
  
  In the following example, these facts are verified. The Tor module does NOT 
  split into the direct sum of the submodules generated in degrees 0 and 1, however.
  
 Example
  S = kk[a,b,c]
  f = (vars S)^[4]
  R = S/ideal f
  p = map(R,S)
  M = coker map(R^2, R^{3:-1}, {{a,b,c},{b,c,a}})			       
  betti (FF =res( M, LengthLimit =>6))
  MS = prune pushForward(p, coker FF.dd_6);
  betti(F = res MS)
  T = exteriorTorModule(f,F);
  betti T
  betti res (PT = prune T)
  ann PT
  PT0 = image (inducedMap(PT,cover PT)* ((cover PT)_{0..12}));
  PT1 = image (inducedMap(PT,cover PT)* ((cover PT)_{13..30}));
  betti res prune PT0
  betti res prune PT1
  betti res prune PT
SeeAlso
  makeModule
///
     doc ///
        Key
	  freeExteriorSummand
	  (freeExteriorSummand,Module)
        Headline
	  find the free summands of a module over an exterior algebra
        Usage
	  F = freeExteriorSummand M
        Inputs
	  M:Module
	    over an exterior algebra
        Outputs
	  F:Matrix
            Map from a free module to M. Image is the largest free summand
	Description
	 Text
         Example
   	    kk= ZZ/101
	    E = kk[e,f,g, SkewCommutative => true]
	    M = E^1++module ideal vars E++E^{-1}
	    freeExteriorSummand M
     ///
       doc ///
          Key
	   submoduleByDegrees
	   (submoduleByDegrees,Module,ZZ)
          Headline
	   submodule generated by elements of bounded degree
          Usage
	   N = submoduleByDegrees(M,n)
          Inputs
	   M:Module
	   L:ZZ
	     n bound for generators
          Outputs
	   N:Module
	     submodule generated by elements of degree <=n
          Description
           Text
	    For testing componentwise linearity, the module should
	    be truncated in degree n
           Example
	    S = ZZ/101[a,b]
	    M = coker random(S^{1,0,-1},S^{-2,-3});
	    prune submoduleByDegrees(M,-1)
	    N = submoduleByDegrees(M,0)
	    betti res prune N
	    betti res truncate(0, prune N)
	  Caveat
	   Text
	    Output is not pruned or truncated
       ///
doc ///
   Key
    cosyzygy
    (cosyzygy, ZZ, Module)
    (cosyzygy, Module)
   Headline
    cosyzygy chain of a Cohen-Macaulay module over a Gorenstein ring
   Usage
    F = cosyzygy(len, M)
   Inputs
    len:ZZ
        how long a chain of cosyzygies
    M:Module
      Should be a CM module over a Gorenstein ring
   Outputs
    F:ChainComplex
      last map is presentation of M
   Description
    Text
     the script returns the dual of the complex F obtained by
     resolving the cokernel of the transpose of 
     the presentation of M
     for len steps. Thus M is the len-th syzygy of the module
     resolved by F. When the second argument len is omitted, 
     the value defaults to len = 2.
    Example
     S = ZZ/101[a,b,c];
     R = S/ideal"a3,b3,c3";
     M = module ideal vars R;
     betti presentation M
     betti (F = cosyzygy(3,M))
     cosyzygy M
///


     doc ///
        Key 
	 Branks
	 (Branks, List)
        Headline 
	 list the ranks of the modules B(d) in a matrixFactorization
        Usage 
	 br = Branks mf
        Inputs 
	 mf:List
	  output of a matrixFactorization computation
        Outputs
	 br: List
	  list of ranks of the modules B(d)
        Description
         Example
	  c = 2
	  S = ZZ/32003[x_0..x_(c-1),a_(0,0)..a_(c-1,c-1)];
	  A = genericMatrix(S,a_(0,0),c,c);
	  f = matrix{{x_0..x_(c-1)}}*map(S^{c:-1},S^{c:-2},A)
	  R = S/ideal f;
	  kR = R^1/ideal(x_0..x_(c-1))
	  MF = matrixFactorization(f,highSyzygy kR)
	  netList Branks MF
	  netList Amats MF
	  netList Bmats MF
	SeeAlso
	  matrixFactorization
	  Bmats
	  Amats
     ///
     doc ///
        Key 
	 Bmats
	 (Bmats, List)
        Headline 
	 list the matrices  d_p in a matrixFactorization
        Usage 
	 bmats = Bmats mf
        Inputs 
	 mf:List
	  output of a matrixFactorization computation
        Outputs
	 bmats: List
	  list matrices $d_p: B_1(p)\to B_0(p)$
        Description
	 Text
	  See the documentation for Branks for an example.
        SeeAlso
	 matrixFactorization
	 Branks
     ///
     doc ///
        Key 
	 Amats
	 (Amats, List)
        Headline 
	 list the matrices  d(p) in a matrixFactorization
        Usage 
	 amats = Amats mf
        Inputs 
	 mf:List
	  output of a matrixFactorization computation
        Outputs
	 amats: List
	  list matrices $d_p: B_1(p)\to B_0(p)$
        Description
	 Text
	  See the documentation for Bmats for an example.
        SeeAlso
	 matrixFactorization
	 Branks
	 Bmats
     ///
     doc ///
        Key
	 sumTwoMonomials
	 (sumTwoMonomials, ZZ,ZZ)
        Headline
	 tally the sequences of Branks for certain examples
        Usage
	 sumTwoMonomials(c,d)
        Inputs
	 c:ZZ
	   codimension in which to work
	 d:ZZ
	   degree of the monomials to take
        Outputs
	 T:Tally
        Description
         Text
	  tallies the sequences of B-ranks that occur for sums of pairs of 
	  monomials in R = S/(d-th powers of the variables), with
	  full complexity (=c); that is,
	  for an appropriate syzygy M of 
	  M0 = R/(m1+m2)
	  where m1 and m2 are monomials of the same degree.
         Example
	  sumTwoMonomials(2,3)
        SeeAlso
	 twoMonomials
	///
	
     doc ///
        Key
	 twoMonomials
	 (twoMonomials, ZZ,ZZ)
	 [twoMonomials,Optimism]
        Headline
	 tally the sequences of Branks for certain examples
        Usage
	 T = TwoMonomials(c,d)
        Inputs
	 c:ZZ
	  codimension in which to work
	 d:ZZ
	  degree of the monomials to take
        Outputs
	 T:Tally
        Description
         Text
	  tallies the sequences of B-ranks that occur for 
	  ideals generated by pairs of 
	  monomials in R = S/(d-th powers of the variables), with
	  full complexity (=c); that is,
	  for an appropriate syzygy M of 
	  M0 = R/(m1, m2)
	  where m1 and m2 are monomials of the same degree.
         Example
	  twoMonomials(2,3)
        SeeAlso
	 twoMonomials
     ///
--docTemplate

end--

restart
--loadPackage "CompleteIntersectionResolutions"
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp CompleteIntersectionResolutions
restart
loadPackage("BGG", Reload=>true)
loadPackage("CompleteIntersectionResolutions", Reload=>true)

--Define the Tate cohomomology of a module over a complete
--intersection (with coefficients in the residue class
--field) to be the result of reducing a high syzygy
--mod a maximal complete intersection and then
--computing the doubly infinite Ext(M,k)
--wild conjecture:

--If we put the cohomology tables of the even and odd ext
--sheaves together and and take into account the
--shift "corresponding" to the change in cohomology degree
--(in some way I haven't quite nailed yet),
--we get exactly the same total numbers as the resolution.
--the last eg below is the most interesting

S = ZZ/101[x,y,z]
R = S/(ideal"x3,y3,z5")
M = R^1/ideal"xy2z3"
E = evenExtModule M
E' = oddExtModule M
degree E
FM = res (M, LengthLimit => 5);
betti res(coker transpose FM.dd_5, LengthLimit =>10)
cohomologyTable(sheaf E,-5,5)
cohomologyTable(sheaf E',-5,5)
--these two sheaves look dual to one another.
--Also:
--If we put these together and and take into account the
--shift "corresponding" to the change in cohomology degree,
--we get exactly the same total numbers as the resolution.

S = ZZ/101[x,y,z]
fff=matrix"x5,y3,z3"
R = S/(ideal fff)
M = R^1/ideal"xyz,x2y2"
M = coker random(R^1, R^{-3,-4})
--M = R^1/ideal"xyz,x2y"
E = evenExtModule M;
E' = oddExtModule M;
--degree E
FM = res (M, LengthLimit => 10);
FFM =res(coker transpose FM.dd_10, LengthLimit =>20);
reverse for i from 0 to 20 list rank FFM_(i)
cohomologyTable(sheaf E,-5,5)
cohomologyTable(sheaf E',-5,5)
--E' has a 1-dimensional component, E does not.
--If we put these together and and take into account the
--shift "corresponding" to the change in cohomology degree,
--we get exactly the same total numbers as the resolution.
--also, the answers seem pretty independent of which powers of x,y,z
--we take!
presentation E
presentation E'
---------------------------------------------
------experiments with makeMFComponents------
---------------------------------------------

-- convert these to use "matrixFactorization" instead
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)
   S = ZZ/101[a,b,c,d]
   mm= ideal vars S
   ff = (matrix"a3,b3,c3,d3")
   ff1 = ff*random(source ff, source ff);
   R = S/(ideal ff);
--   P = prune( R^1/(ideal vars R)^2)
--   P = coker random(R^2, R^{-1, -2})
   P = coker map(R^1, R^{-2,-3}, matrix"a2,bcd")
   FF = res(P, LengthLimit =>10)
   betti FF
   M = coker FF.dd_8;
   MF = matrixFactorization(ff1,M);
   
   


kk= ZZ/5
S = kk[x,y]
ff=matrix"x4,y4"
R = S/ideal ff

m= coker random(R^2, R^{2:-2})
betti res( m, LengthLimit=>10)


-- Are there modules of complexity 2 (linear resolution growth) whose betti numbers do NOT grow strictly?
-- for codim 2 it would be enough for rank(B_1(2)) = rank (B_0(2))= b. Then if rank B_0(1) = a we would have
-- Betti sequence a+b a+b 2a+b 2a+b .... .

--Start over R(1) = S/f_1 with a square matrix whose cokernel is killed by f_2. Then the kernel is CM, so has periodic
--resolution. IF the homotopies are all minimal then we're in.

S = kk[a,b,c]
--R = S/(c*ideal"a3+b3+c3")
R = S/ideal"a3b3c3"
m = random(R^2, R^{2:-1})

f2 = det m
R2 = R/(ideal f2^2)
m2 = sub(m, R2)
betti res (coker m2, LengthLimit => 10)

-------------
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp makeHomotopies


kk= ZZ/101
S = kk[a,b,c,d]
--m = random(S^3, S^{3:-1, 3:-2})
m = random(S^2, S^{5:-1})
m = random(S^1, S^{5:-2})
m = random(S^1, S^{4:-2}) -- complete intersection
M = coker m
F = res M
betti F
f = matrix"a5,b5"
f**M
homot = makeHomotopies(f,F,5)
homot = makeHomotopies(f,F)
homot = makeHomotopies(f_{1},F)
L = sort select(keys homot, k->(homot#k!=0 and sum(k_0)>1))
#L
netList L
k1 =S^1/(ideal vars S)
select(L,k->(k1**homot#k)!=0)
homot#(L#1)
apply(L, k->(homot#k)

-------------
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"

--
--In this example the even part of the Ext has different
--associated primes from the odd part. This shows up in the
--S2-ification. 
--
restart
loadPackage "CompleteIntersectionResolutions"
kk= ZZ/101
S = kk[a,b,c]
R = S/ideal"a4,b4,c4"
M1 = R^1/ideal"a2b,c2a,abc,a3c" -- Example 1
betti(F= res(M1,LengthLimit =>5))
M0 = coker transpose F.dd_5;
betti( res(M0,LengthLimit =>10))

Eodd = prune oddExtModule M0;
Eeven = prune evenExtModule M0;
--error topComponents Eeven
prune removeLowestDimension Eodd
hf(-10..5, Eodd)
hf(-10..5, target S2(-5,Eodd))
hf(-10..5, removeLowestDimension target S2(-5,Eodd))
hf(-10..5, removeLowestDimension Eodd)
hf(-10..5, topComponents minimalPresentation Eodd)
toString minimalPresentation Eodd
minimalPresentation topComponents Eodd

use S



viewHelp removeLowestDimension
viewHelp top
p=-3
f=S2(p,E);
hf(-5..5,coker f) 

E = Eodd 
p= -3
f=S2(p,E);
hf(p..10,coker f)

betti prune f
--In Example 1, the odd part of Ext has an associated prime of dim 1, 
-- but the even part does not. Thus S2-ification of the odd part is infinite
--but it's in the Ext module, too! At least as far as I carried
--the computation, the map from the Ext module onto its S2-ification
--is surjective.

---
--The exterior module structure of Tor
installPackage "CompleteIntersectionResolutions"
viewHelp CompleteIntersectionResolutions
restart
loadPackage ("CompleteIntersectionResolutions", Reload=>true)

S = kk[a,b,c]
f = (vars S)^[4]
R = S/ideal f
p = map(R,S)
M = coker map(R^2, R^{3:-1}, {{a,b,c},{b,c,a}})			       
--gives non-linear phi and phi1,
--The tor module has a free summand
--E1^6 ++ E1(-1)^9
--over the 2-variable exterior alg.


M = coker map(R^1, R^{ -2}, {{a^2+b^2+c^2}})
--gives linear phi and phi1,
--The tor module has a free summand
--E1^5 ++ E1(-1)^9
--over the 2-variable exterior alg.
--but the complement has annihilator
--only e_0*e_1, so is not
--a sum of simple modules.

time betti (FF =res( M, LengthLimit =>6))
MS = prune pushForward(p, coker FF.dd_6);
--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
time T = exteriorTorModule(f,F);
TateResolution T
betti res prune truncate(1,submoduleByDegrees(T,1))


betti res coker submatrixByDegrees(PTR.dd_1,{0},{1})
ME = (transpose ((PTR.dd_1)_{0..26}))_{0..13}
betti res coker ME
ann PT
phi = presentation PT;
isLinear phi -- is phi equivalent to a linear matrix??
trim minors(1, phi)


PT0 = submoduleByDegrees(PT,0);
PT1 = submoduleByDegrees(PT,1);
betti res prune PT0
betti res prune PT1
PT0+PT1 == PT
degree intersect(PT0,PT1)
betti res prune PT


--codim 2 generic examples
installPackage "CompleteIntersectionResolutions"
viewHelp CompleteIntersectionResolutions
restart
loadPackage "CompleteIntersectionResolutions"
S = kk[a,b]
f = (vars S)^[4]
R = S/ideal f
p = map(R,S)
matrix{{a,b,0}}||random(R^1,R^{3:-2})
N = coker map(R^{0,1}, R^{3:-1}, matrix{{a,b,0}}||random(R^1,R^{3:-2}))
M = coker random(R^{2:0}, R^{3:-2})
M = Hom(N,R)
regularity ExtModule M
len = 4
time betti (FF =res( M, LengthLimit =>len))
MS = prune pushForward(p, coker FF.dd_len);
--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
time T = exteriorTorModule(f,F);
betti T
betti res (PT = prune T)
degree T
hf(-4..4, T)
betti res prune Hom(T,T)

degree M

ann PT
phi = presentation PT;
isLinear phi -- is phi equivalent to a linear matrix??
trim minors(1, phi)


PT0 = submoduleByDegrees(PT,0);
PT1 = submoduleByDegrees(PT,1);
betti res prune PT0
betti res prune PT1
PT0+PT1 == PT
degree intersect(PT0,PT1)
betti res prune PT

--f1 = (vars S)_{0,1}^[4]
f1 = (vars S)^[4] * random(S^{3:-4}, S^{2:-4})
time T1 = exteriorTorModule(f1,F);
betti T1
betti (PT1 = prune T1)
ann PT1
phi1 = presentation PT1;
isLinear phi1
FT1 = freeExteriorSummand PT1;
prune image FT1
gens ann (PT1/image FT1)
hf(0..2,PT1/image FT1)


betti res PT

---
restart
loadPackage "CompleteIntersectionResolutions"

S = kk[a,b,c,d]
f = (vars S)^[4]
R = S/ideal f
p = map(R,S)
M = R^1/ideal"a2b+bc2,ac+b2,c3d3" -- an example in 4 vars

regularity evenExtModule(M)
regularity oddExtModule M
len = 6
time betti (FF =res( M, LengthLimit =>len))

MS = prune pushForward(p, coker FF.dd_len);

--the pruned presentation of tor starts with FF.dd_5
betti(F = res MS)
time T = exteriorTorModule(f,F);
TateResolution(T,5,10)
betti T
betti res (PT = prune T)
ann PT
phi = presentation PT;
isLinear phi -- is phi equivalent to a linear matrix??
trim minors(1, phi)


PT0 = submoduleByDegrees(PT,0);
PT1 = submoduleByDegrees(PT,1);
betti res prune PT0
betti res prune PT1
PT0+PT1 == PT
degree intersect(PT0,PT1)
betti res prune PT

--f1 = (vars S)_{0,1}^[4]
f1 = (vars S)^[4] * random(S^{3:-4}, S^{2:-4})
time T1 = exteriorTorModule(f1,F);
betti T1
betti (PT1 = prune T1)
ann PT1
phi1 = presentation PT1;
isLinear phi1
FT1 = freeExteriorSummand PT1;
prune image FT1
gens ann (PT1/image FT1)
hf(0..2,PT1/image FT1)


betti res PT

------------


--simplest makeMF examples:
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
viewHelp "CompleteIntersectionResolutions"

restart
loadPackage("CompleteIntersectionResolutions", Reload =>true)
--generic codim 2 complete intersection example:
--one CI mod another:
c = 3
-- c=4 is easy, for c=5 the resolution step takes longer than I wanted to wait
--S = ZZ/32003[a_(0,0)..a_(c-1,c-1),x_0..x_(c-1)];
--x first order seems slightly easier to understand.
S = ZZ/32003[x_0..x_(c-1),a_(0,0)..a_(c-1,c-1)];
A = genericMatrix(S,a_(0,0),c,c);
f = matrix{{x_0..x_(c-1)}}*map(S^{c:-1},S^{c:-2},A)
R = S/ideal f;
kR = R^1/ideal(x_0..x_(c-1))
netList (MF = matrixFactorization(f,highSyzygy (kR,Optimism=>0)))
toArray toList(0..2)
netList Branks MF
netList Bmats MF

MF = matrixFactorization(f,highSyzygy (kR,Optimism=>-1))--first syzy -- fails for c>= 2
--if c=1 then kR is already a high syzygy; 
netList Branks MF

Amats MF

restart
loadPackage("CompleteIntersectionResolutions", Reload =>true)
--specialization to the case where A is diagonal (faster!)
c = 2
S = kk[a_0..a_(c-1),x_0..x_(c-1)];
A = diagonalMatrix(S, toList(a_0..a_(c-1)))
f = matrix{{x_0..x_(c-1)}}*A
R = S/ideal f;
kR = R^1/ideal(x_0..x_(c-1));
time F = res(kR, LengthLimit =>c+2);
M = coker F.dd_(c+1)
time MF = matrixFactorization(f,M)
Bmats MF
f
netList Branks MF


--residue field ranks -- still faster
--and they don't depend on which power of the vars
--defines the ring
resFieldMFRanks = (c,d) ->(
S = ZZ/101[x_0..x_(c-1)];
d = 2;
ff = map(S^1,S^{c: -d}, (i,j)->x_j^d);
R = S/ideal ff;
kR = R^1/ideal vars R;
F = res(kR,LengthLimit=> c+2);
M = coker F.dd_(c+1);
Branks matrixFactorization(ff, M))

for c from 2 to 7 do(
    <<netList resFieldMFRanks(c,2)
--    << resFieldMFRanks(c,2)==resFieldMFRanks(c,3)<<endl;
    <<endl;
    )

restart
loadPackage("CompleteIntersectionResolutions", Reload =>true)
-- twoMonomials searches for pairs of monomials of degree d
-- in the given ring (mod the c d-th powers of the variables) 
--of complexity c (that is,
--dim Ext(R/(m1, m2),k)=c), and tallies the sequence of B ranks
--for a high syzygy of R/(m1,m2).

--Conclusion: in every one of these cases, the sequences
--{rank target B(i)} and {rank source B(i)} are *strictly increasing
--for i = 2..4 (and weakly increasing between i = 1,2.)
--also, the multiplicity is always 8, 12 or 17.

twoMonomials(3,3) -- with Optimism => 1 it fails.
twoMonomials(3,4)
twoMonomials(3,5)
twoMonomials(4,3)

------
--What about R/m1+m2, the sum of two monomials?
--sumtwoMonomials(c,d,S)
--tallies the sequences of B-ranks that occur for sums of pairs of 
--monomials in R = S/(d-th powers of the variables), with
--full complexity (=c); that is,
--for an appropriate syzygy M of 
--M0 = R/(two monomials of the same degree)

----------RUNS of sumTwoMonomials
sumTwoMonomials(3,3)
sumTwoMonomials(3,4)
sumTwoMonomials(3,5)


----------------------
--is the "Orlov" factorization at a point the same for all cosyzygies?
restart
loadPackage("CompleteIntersectionResolutions", Reload =>true)
--viewHelp matrixFactorization

kk=ZZ/101
S = kk[a,b,s,t]
R = S/ideal(a^3, b^3)
p = map(R,S)
kkk = R^1/ideal(a,b)
G = cosyzygy(6, kkk)
M = coker transpose G.dd_1
MS = pushForward(p, M)
use S
T = S/ideal(s*a^3+t*b^3)
MT = T**MS
betti (F = res MT)

use S
T' = kk[a,b]/ideal(a^3+b^3)
q = map(T',T,{a,b,1_T',1_T'})
m = q F.dd_4
betti res prune coker m
betti res(T'^1/ideal(a,b), LengthLimit=>5)


-------------
--Can B_0(2) = 0 in a codim 2 mf?
S = ZZ/101[a_(0,0)..a_(1,1),y_0,y_1]
d1 = transpose genericMatrix(S,a_(0,0),2,2)
d2 = matrix{{y_0},{y_1}}
d = d1|d2
M = coker d
betti res M
f1 = det d1
f2 = (d1^{0})*d2
ff = matrix{{f1}}|f2
fff = ff*random(source ff, source ff)
matrixFactorization(fff,M)


--an example to show that the Poincare series
--of a module over a CI R and the same module over
--the regular ring Q are not always related by
--P^Q >= (1+t)P^r.
Q = kk[a,b,c]
R = Q/ideal"a2+b2+c2"
kR = R^1/ideal vars R
betti (FR = res kR)
M = coker transpose FR.dd_2
betti res M
MQ = pushForward(map(R,Q),M)
betti res MQ

----------


--Orlov MF of a syzygy =? Orlov MF? NO!
--***maybe this is because we are not working over the
--projective space!
--in any case, if M is a high syzygy over R, it looks from 
--the betti tables as if
--OrlovMF(M) is a summand of OrlovMF(second syzygy of M)
--In fact, it looks as though you are
--adding a fixed module every even (every odd) syzygy


restart
loadPackage ("CompleteIntersectionResolutions", Reload => true)
S = ZZ/101[a,b,c]
ff = matrix"a3,b3"
R = S/ideal ff
M = R^1/ideal vars R
M = coker random(R^2,R^{3:-2})

T = S[A_0..A_(numcols ff-1)]
phi = map(T,S)
betti (FF = OrlovMF(ff,M))
betti (FF = OrlovMF(ff,M,phi,4))

B1 = (Bmats matrixFactorization(ff,highSyzygy M))_0
betti B1
FR = res(M, LengthLimit =>9)
p
(Bmats matrixFactorization(ff,highSyzygy M))_0
netList apply(length FR,j-> betti OrlovMF(ff,coker FR.dd_(j+1)))
(Bmats matrixFactorization(ff,highSyzygy M))_0

--after localizing, we're just working mod a general element
--of the regular sequence. Let's try that!

---------------------
S= ZZ/101[x,y,z]
R1 = S/ideal"xz"
d = matrix"z,-y,0;0,x,y"
M2 = coker d
betti res M2
ann M2
R2 = R1/ideal"y2"
M22 = R2**M2
betti(F= res M22)
F.dd_2

viewHelp symExt
S = kk[a,b,c]
M=presentation module ideal"a,b"
symExt(M,S)

--------------------
--Walker's example
--resolve the complex P = (syz_2 k)^2 --> k 
--over R = k[x,y,z]/(x^m,y^m,z^m).
--Stable ext (P,k) presumably does not surject onto
--H^0_*(sheaf ext).
restart
loadPackage("CompleteIntersectionResolutions", Reload => true)
uninstallPackage ("CompleteIntersectionResolutions")
installPackage ("CompleteIntersectionResolutions")
S = ZZ/101[x,y,z]
m= 3
ff = matrix{{x^m,y^m,z^m}}
R = S/ideal ff
kR = R^1/ideal vars R
FF = res(kR, LengthLimit => 8)
--viewHelp makeT
T = makeT(ff, FF, 2)

FF2 = R^{3}**truncate(2, FF)
betti FF2
betti FF
--u0=map(FF_0,(FF2_0),T_0)
--u1=map(FF_0,(FF2_0),T_1)
GG = FF2++FF2
u = map(FF_0,(GG_0),T_0|T_1)

uu=extend(FF,GG,u);
phi = map((GG_0)++FF_1,(GG_1)++FF_2, matrix{{GG.dd_1, 0},{uu_1, FF.dd_2}});
M = coker phi;
--betti res M

--viewHelp cosyzygy
N = coker (cosyzygy(10, M)).dd_1;
Eeven = evenExtModule N;
Eodd = oddExtModule N;

cohomologyTable(sheaf Eeven, 0,10)
hf(-1..10, Eeven)
cohomologyTable(sheaf Eodd, 0,10)
hf(0..10, Eodd)
--viewHelp S2
coker S2(0, Eeven) == 0
hf(-1..10, target S2(0, Eeven))
truncate(0,coker S2(0, Eeven)) ==0


-------
restart
SE=kk[a,b,c,e,f, SkewCommutative =>{e,f}]
phi = matrix{{a,b,c,e,f,0,0},{c,a,b,0,0,e,f}}
M = coker phi
K = ker phi
kSE = SE^1/ideal(a,b,c)
p = map(kSE, SE^1, gens kSE)
coker prune Hom(K,p) == 0
Ext1(M,kSE)
code methods Ext


Ext1(M,kSE)


