
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
    print "next command causes the crash";
--    error();
    extend(dsum(rank source phi, K), 
	dsum(rank target phi,R^{2}**K2), 
	phiT)    
        )
end

restart
load "bug-extend.m2"
  kk = ZZ/101;
  S = kk[a,b,c];
  ff = matrix{{a^2, b^2}};
  R = S/ideal ff;
  Ops = kk[x_1,x_2]
  MM = Ops^1/ideal(x_1^2*x_2)  
  moduleAsExt(MM,R)

