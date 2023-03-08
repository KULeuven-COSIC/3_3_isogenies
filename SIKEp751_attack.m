/*
This file contains an implementation of an attack on Alice's secret isogeny in the SIKEp751 protocol.
We start by defining certain hardcoded parameters which are needed throughout the entire protocol.
*/

clear;
a := 372;
b := 239;

p := 2^a*3^b - 1;
Fp2<I> := GF(p, 2);
R<x> := PolynomialRing(Fp2);

// The following are needed as inverses for the BFT-evaluation formulae.
INV2 := Fp2 ! 1/2; INV3 := Fp2 ! 1/3; INV4 := Fp2 ! 1/4; INV16 := Fp2 ! 1/16; INV216 := Fp2 ! 1/216; INV864 := Fp2 ! 1/864;
INV103680 := Fp2 ! 1/103680; INV213408 := Fp2 ! 1/213408; INV13837824 := Fp2 ! 1/13837824; INV8115344640 := Fp2 ! 1/8115344640; INV327019680 := Fp2 ! 1/327019680;

// We need a non-square for certain twists.
j := 1; repeat NSQ := (I + j); j +:= 1; until not IsSquare(NSQ);

//This is the starting curve in the SIKE protocol for all security levels.
E_start := EllipticCurve(x^3 + 6*x^2 + x);
infty := E_start ! 0;

// We (naively) compute 2^a- and 3^b-torsion bases instead of hardcoding them.
repeat PA := 3^b*Random(E_start);
until 2^(a-1)*PA ne infty;
repeat QA := 3^b*Random(E_start);
until WeilPairing(PA, QA, 2^a)^(2^(a-1)) ne 1;

repeat PB := 2^a*Random(E_start);
until 3^(b-1)*PB ne infty;
repeat QB := 2^a*Random(E_start);
until WeilPairing(PB, QB, 3^b)^(3^(b-1)) ne 1;

/*
We will now precompute the (u+2*v*i)-endomorphism used in the attack SIKEp751.
Remark that this is NOT part of the standard set-up. However, it can be done offline so we ignore it for timing purposes.
Either way, this computation takes no time whatsoever.
*/

// We first compute the needed two_i endomorphism (naively but efficient)
E1728, phi := IsogenyFromKernel(E_start, x);
for iota in Automorphisms(E1728) do
  P := Random(E1728);
  if iota(iota(P)) eq -P then
    two_i := phi*iota*DualIsogeny(phi);
    break;
  end if;
end for;

u := 84727936279133751413846965905657949516597707407463528877;
v := 252700408455552999199462036016877991153973776652061243550;
// Sanity check:
assert 3^238 - 10*2^372 eq (u+2*v*I)*(u-2*v*I);

/*
We now define the public 2^a- and 3^b-torsion points that Alice and Bob work with.
Remark that we worked the opposite route and typically this is given first, and not the points after the endomorphism.
Again, this doesn't matter since it takes no time and can be done in a precomputation.
*/
PA_pub := u*PA + v*two_i(PA);
QA_pub := u*PA + v*two_i(QA);
PB_pub := u*PB + v*two_i(PB);
QB_pub := u*QB + v*two_i(QB);


/*
The following function lets Alice generate a random 2^a-subgroup and execute her first part of the SIKE protocol.
*/
function Alices_computation(E_start, PA_pub, QA_pub, PB_pub, QB_pub)
	repeat k_A_private := Random(2^a);
	KA := PA_pub + k_A_private*QA_pub;
	until 2^(a-1)*KA ne infty;

	// Naive implementation of 2^a-isogeny computation but fast enough for testing
	order := 2^a;
	EA := E_start;
	phiPB := PB_pub;
	phiQB := QB_pub;
	while order ne 1 do
		local_kernel := (order div 2)*KA;
		EA, phiA := IsogenyFromKernel(EA, x-local_kernel[1]);
		order div:= 2;
		KA := phiA(KA);
		phiPB := phiA(phiPB);
		phiQB := phiA(phiQB);
	end while;

	return k_A_private, EA, phiPB, phiQB;

end function;


/*
Our first step is gluing the elliptic curves along their a 3-torsion subgroup so we put these functions first.
*/
function transform_ell_point(pt, alpha,beta,gamma)
	if pt[3] eq 0 then
		return [0,1,0];
	else 
		u := pt[1];
		v := pt[2];
		return [(u-beta)/alpha, gamma*v,1];
	end if;
end function;


function apply_product_transformation(transform, points)
    trafo1, trafo2 := Explode(transform);
    alpha1,beta1,gamma1 := Explode(trafo1);
    alpha2,beta2,gamma2 := Explode(trafo2);
    images := [];
    for pt in points do
        pt1, pt2 := Explode(pt);
        im1 := transform_ell_point(pt1, alpha1,beta1,gamma1);
        im2 := transform_ell_point(pt2, alpha2,beta2,gamma2);
        images := Append(images, [im1,im2]);
    end for;
    return images;
end function;


function eval_phi1(pt, a,b,c,d) 
	/* Evaluation of the pull-back of phi1 */
	if pt[3] eq 0 then
		return 0;
	else 
		Delta1 := a^3+b^2;
		Delta2 := c^3+d^2;
		u1 := pt[1];
		v1 := pt[2];
		denA := (2*u1 - (12*c*b-16*d*a^2))^2 + a;
		R<x> := PolynomialRing(Parent(a));
		if denA eq 0 then
			print("not implemented");
			return [];
		else 
			A1 := -4*(a*u1+8*d*Delta1);
			A0 :=  -8*(b*u1-6*c*Delta1);
			B1 :=  -2*v1*( (2*u1 + 4*(4*a^2*d - 3*b*c))^3 +  2*(3*a*u1 + 6*a*(4*a^2*d  - 3*b*c) + b));
			B0 := -4*v1/a^2*(4*a*(a*u1 +  8*d*Delta1)^2 - a*Delta1);
			A := x^2 + A1/ denA *x  +A0 / denA;
			B := B1/denA^2*x+B0/denA^2;
			return [A,B];
		end if;
	end if;
end function;


function eval_phi2(pt, a,b,c,d) 
	/* Evaluation of the pull-back of phi2 */
	if pt[3] eq 0 then
		return  0;
	else 
		Delta1 := a^3+b^2;
		Delta2 := c^3+d^2;
		u2 := pt[1];
		v2 := pt[2];
		denC  :=  -8*(d*u2 - 2*(Delta2)*3*a);
		R<x> := PolynomialRing(Parent(a));
		if denC eq 0 then
			print("not implemented");
			return [];
		else 
			C1 :=  -4*(c*u2  + 8*b*Delta2);
			C0 := (2*u2 + (16*b*c^2 - 12*a*d))^2 + c;
			D1 :=  16*v2*(Delta2); 
			D0 := v2*(-8*b) * ((768*a*b^2*c - 64*b^2)*u2^2 + (12288*a*b^3*c^3 + 6912*a^3*b*c^2 - 1152*a^2*b*c + 48*a*b)*u2 + 49152*a*b^4*c^5 + 55296*a^3*b^2*c^4 + 15552*a^5*c^3 + 4096*b^4*c^4 - 4608*a^2*b^2*c^3 - 3888*a^4*c^2 - 192*a*b^2*c^2 + 324*a^3*c + 16*b^2*c - 9*a^2);
			C :=  x^2 + C1 /denC *x +  C0/denC;
			D := D1/denC^2*x + D0/(16*b^2*denC)^2;
			return  [C,D];
		end if;
	end if;
end function;


function get_ABCD_transform(kernel,curves)
    E1, E2 := Explode(curves);
	P1 := kernel[1][1];
	P2 := kernel[1][2];
	Q1 := kernel[2][1];
	Q2 := kernel[2][2];

	f1 := HyperellipticPolynomials(E1);
	f2 := HyperellipticPolynomials(E2);
	Knew<aux1,aux2,a,b,c,d,alpha1,beta1,beta2,gamma1> := PolynomialRing(Fp2,10,"lex");
    Lnew<aux1,aux2,a,b,c,d,alpha1,beta1,beta2,gamma1> := FieldOfFractions(Knew);
        gamma2 := 1;
        alpha2 := 1;
        Kx<x> := PolynomialRing(Lnew);
	Delta1 := a^3+b^2;
	Delta2 := c^3+d^2;
	/* 
	Apply coordinate transformation x = alpha*xprime + beta and y = yprime/gamma
	Inverse is xprime = (x-beta)/alpha and yprime = gamma*y
	*/
	newf1 := gamma1^2*Evaluate(f1, alpha1*x+beta1);
	newf2 := gamma2^2*Evaluate(f2, alpha2*x+beta2);
	
	f1_abc := x^3 + 12*(2*a^2*d - b*c)*x^2 +12*(16*a*d^2 + 3*c^2)*Delta1*x + 512 * Delta1^2*d^3;
	f2_abc := x^3 + 12*(2*b*c^2 - a*d)*x^2 +12*(16*b^2*c + 3*a^2)*Delta2*x + 512 * Delta2^2*b^3;
	
	rel1 := [12*a*c + 16*b*d -1, aux1*Delta1-1, aux2*Delta2-1];
	rel2 := Coefficients(f1_abc - newf1) cat Coefficients(f2_abc - newf2);
	
	/* Condition on the kernel*/
	newP1 := transform_ell_point(P1,alpha1,beta1,gamma1);
	newP2 := transform_ell_point(P2,alpha2,beta2,gamma2);
	newQ1 := transform_ell_point(Q1,alpha1,beta1,gamma1);
	newQ2 := transform_ell_point(Q2,alpha2,beta2,gamma2);
	
        
	imP1 := eval_phi1(newP1,a,b,c,d);
	imP2 := eval_phi2(newP2,a,b,c,d);
	imQ1 := eval_phi1(newQ1,a,b,c,d);
	imQ2 := eval_phi2(newQ2,a,b,c,d);

	rel3 := [Knew! Numerator(el) : el in Coefficients(imP1[1] - imP2[1])];
	rel4 := [Knew! Numerator(el) : el in Coefficients(imQ1[1] - imQ2[1])];
	rel5 := [Knew! Numerator(el) : el in Coefficients(imP1[2] + imP2[2])];
	rel6 := [Knew! Numerator(el) : el in Coefficients(imQ1[2] + imQ2[2])];;
	
	I := ideal<Knew | rel1 cat rel2 cat rel3 cat rel4 cat rel5 cat rel6>;
	GB := GroebnerBasis(I);
	a := -Coefficients(GB[3])[2];
	b := -Coefficients(GB[4])[2];
	c := -Coefficients(GB[5])[2];
	d := -Coefficients(GB[6])[2];
	alpha1 := -Coefficients(GB[7])[2];
    alpha2 := 1;
	beta1 := -Coefficients(GB[8])[2];
	beta2 := -Coefficients(GB[9])[2];
	gamma1 := Roots(UnivariatePolynomial(GB[10]))[1][1];
	gamma2 := 1;
	
	return  a,b,c,d, [alpha1,beta1,gamma1], [alpha2,beta2,gamma2];
end function;


function get_hyperelliptic_codomain_curve(a,b,c,d)
    Kx<x> := PolynomialRing(Fp2);
    F1 := x^3 + 3*a*x + 2*b;
    F2 := 2*d*x^3 + 3*c*x^2 + 1;
    return F1*F2;
end function;


function glue_evaluation(kernel, points,curves)
	/*
	Input: kernel generators of the (3,3) gluing, i.e. two pairs of points (P1,P2), (Q1,Q2) in E1 x E2, and additional points on the product.
	Output: the Jacobian of a genus-2 curves, as well as the images of points under the isogeny.
	*/
        E1, E2 := Explode(curves);
	P1 := kernel[1][1];
	P2 := kernel[1][2];
	Q1 := kernel[2][1];
	Q2 := kernel[2][2];
	f1 := HyperellipticPolynomials(E1);
	f2 := HyperellipticPolynomials(E2);
	A,B,C,D, transform1, transform2 := get_ABCD_transform(kernel, [E1,E2]);	
	transform_points := apply_product_transformation([transform1,transform2], points);
	F := get_hyperelliptic_codomain_curve(A,B,C,D);
	CC := HyperellipticCurve(F);
	JJ := Jacobian(CC);
	codomain_points := [];
	for pt in transform_points do
		new_pt := JJ ! eval_phi1(pt[1], A,B,C,D) + JJ ! eval_phi2(pt[2], A,B,C,D);
		Append(~codomain_points, new_pt);
	end for;
	return JJ, codomain_points;
end function;


/*
After the gluing we'll need to do (3,3)-isogenies between Jacobians.
*/

function get_cubic_Gx(D)
	Kab<alpha,beta,lambda> := PolynomialRing(Fp2,3);
	Kx<x> := PolynomialRing(Kab);
	F := HyperellipticPolynomials(Curve(Parent(D)));
	pol := F - (D[2] + (alpha*x + beta)*D[1])^2 - lambda*(Kx ! D[1])^3;
	relations := [Eltseq(pol)[i] : i in [1..4]];
	GB := GroebnerBasis(Ideal(relations));
	alpha := -Coefficients(GB[1])[2];
	beta := -Coefficients(GB[2])[2];
	Gx := D[2] + (alpha*x + beta)*D[1];
	return Eltseq(Gx);
end function;


function get_rst_transform(Ti)

	Knew<newr,news,newt,b,c,d,e,newtinv> := PolynomialRing(Fp2,8,"grevlex");
	Kx<x> := PolynomialRing(Knew);
	
	T1 := Ti[1]; T2 := Ti[2];
	Gx1 := Kx ! get_cubic_Gx(T1);
	Gx2 := Kx ! get_cubic_Gx(T2);
	Hx1 := Kx ! T1[1];
	Hx2 := Kx ! T2[1];
	
	I0 := [newt*newtinv - 1]; // Assertion such that t =/= 0

	G1 := ((news - news*newt - 1)*x^3 + 3*news*(newr - newt)*x^2 + 3*news*newr*(newr - newt)*x - news*newt^2 + news*newr^3 + newt);
	Gx1eval := Kx ! Numerator(Evaluate(Gx1,(x + b)/(c*x + d))*(c*x + d)^3);
	I1 := [e*Eltseq(G1)[i] - Eltseq(Gx1eval)[i] : i in [1..4]];

	G2 := ((news - news*newt + 1)*x^3 + 3*news*(newr - newt)*x^2 + 3*news*newr*(newr - newt)*x - news*newt^2 + news*newr^3 - newt);
	Gx2eval := Kx ! Numerator(Evaluate(Gx2,(x + b)/(c*x + d))*(c*x + d)^3);
	I2 := [e*Eltseq(G2)[i] - Eltseq(Gx2eval)[i] : i in [1..4]];

	H1 := x^2 + newr*x + newt;
	Hx1eval := Kx ! Numerator(Evaluate(Hx1,(x + b)/(c*x + d))*(c*x + d)^2);
	I3 := [LeadingCoefficient(Hx1eval)*Eltseq(H1)[i] - Eltseq(Hx1eval)[i] : i in [1..2]];

	H2 := x^2 + x + newr;
	Hx2eval := Kx ! Numerator(Evaluate(Hx2,(x + b)/(c*x + d))*(c*x + d)^2);
	I4 := [LeadingCoefficient(Hx2eval)*Eltseq(H2)[i] - Eltseq(Hx2eval)[i] : i in [1..2]];

	I := Ideal(I0 cat I1 cat I2 cat I4);	// Yields quickest results on average
	GB := GroebnerBasis(I);
	
	r := -Coefficients(GB[1])[2];
	s := -Coefficients(GB[2])[2];
	t := -Coefficients(GB[3])[2];
	
	a := 1;
	b := -Coefficients(GB[4])[2];
	c := -Coefficients(GB[5])[2];
	d := -Coefficients(GB[6])[2];
	e := -Coefficients(GB[7])[2];
	
	return [r,s,t], [a,b,c,d,e];

end function;


function apply_transformation(transform, points, f, rst)

	r,s,t := Explode(rst);
	Kx<x> := PolynomialRing(Parent(r));
	f_rst := ((-s*t + s - 1)*x^3 + (-3*s*t + 3*s*r)*x^2 + (-3*s*t*r + 3*s*r^2)*x - s*t^2 + s*r^3 + t)^2 + 4*s*(x^2 + r*x + t)^3;
	C := HyperellipticCurve(f_rst);
	J := Jacobian(C);
	newK := KummerSurface(J);
	a,b,c,d,e := Explode(transform);
	f0,f1,f2,f3,f4,f5,f6 := Explode(Coefficients(f));
	ac := a*c;
	bd := b*d;
	abcd := ac*bd;
	bcpad := b*c + a*d;

	l0 := (-2) * (ac)^2 * (3*(bcpad)^2 - 8*abcd)*f0 + (2) * ac * (bcpad) * ((bcpad)^2 - 2*abcd)*f1 + (-4) * abcd * ((bcpad)^2 - 2*abcd) * f2 + bd * (bcpad)^3 * f3 + (-2) * (bd)^2  * (bcpad)^2* f4 + (4) * (bd)^3 * (bcpad) *f5 + (-8) * (bd)^4 *f6 ;
	l1 := (-4) * (ac)^3 * (bcpad)*f0 + (ac)^2 * ((bcpad)^2 + 4*abcd) * f1 + (-4) * abcd*a*c * (bcpad)*f2 + abcd * ((bcpad)^2 + 4*abcd)*f3 + (-4) * ac * (bd)^2 * (bcpad)*f4 + (bd)^2 * ((bcpad)^2 + 4*abcd)* f5 + (-4) * (bd)^3 * (bcpad)*f6;
	l2 := (-8) * (ac)^4 *f0 + (4) * (ac)^3 * (bcpad) *f1 + (-2) * (ac)^2 * (bcpad)^2 * f2 + ac * (bcpad)^3*f3 + (-4) * abcd * (b^2*c^2 + a^2*d^2) * f4 + (2) * bd * (bcpad) * (b^2*c^2 + a^2*d^2) * f5 + (-2) * (bd)^2 * (3*b^2*c^2 - 2*abcd + 3*a^2*d^2) * f6;

	images := [];
	for xx in points do
		y1 := xx[3]*c^2 + xx[2]*c*d + xx[1]*d^2;
		y2 := 2*xx[3]*a*c + xx[2]*(bcpad) + 2*xx[1]*b*d;
		y3 := xx[3]*a^2 + xx[2]*a*b + xx[1]*b^2;
		y4 := e*((a*d-b*c)^4*xx[4] + l2*xx[3] + l1*xx[2] + l0*xx[1]);
		images := Append(images,newK![y1,y2,y3,y4]);
	end for;

	return images;
end function;


function get_codomain_Kummer_coefficients(rst)
	
	r,s,t := Explode(rst);
	e1 := s;
	e2 := t;
	e3 := r - 1;
	e4 := r - t;
	e5 := r*s - s*t - 1;
	e6 := r^2 - t;
	Delta := (e1*e3*e6)^2 + e5*(e3*e6*(e1*e4 + e5) + e4^2*e5);
	if Delta eq 0 then return Delta, 0, 0, 0, 0; end if;
	
	invD := 1/Delta;

	j0fac := e1*( e1*( e1*( e6^2*( e6^2*(e4*e5 + e3) - e3*e4^2*(e3 + 1)) + (e2*e3*e4)^2*e4*e5) - e4*e5*(e2*e4^3 + e6^3)) + e2*(e2*Delta + e4^2*e5*(2*e5*e6 + e6)));
	j1fac := e1*( e1*( e6^3*( e5*(e1*e4^2 + e2 - 1) + e1*e3^2) + (e2*e3)^2*e3*e4*e5*(2 - e1*e4)) + e2*(Delta - e2*e3^3*e5));
	j2fac := e1*(e2*( Delta - (e3*e5)^2*e6*(2*e5 + 1)) + e1*e4^2*Delta );

	j0 := 36*Delta*j0fac;
	j1 := 12*Delta*j1fac;
	j2 := 36*Delta*j2fac;

	Kx<x> := PolynomialRing(Parent(r));
	Hrst := x^2 + r*x + t;
	Grst := (s - s*t - 1)*x^3 + 3*s*(r - t)*x^2 + 3*r*s*(r - t)*x + (r^3*s - s*t^2 + t);
	Frsti := Coefficients(Delta*(Grst^2 + 4*s*Hrst^3));
	f0D := Frsti[1]; f1D := Frsti[2]; f2D := Frsti[3]; f3D := Frsti[4]; f4D := Frsti[5]; f5D := Frsti[6]; f6D := Frsti[7];
	Hrst_tilde := e3*e5*x^2 + (r^3*s - 2*r^2*s + r*s*t + r - s*t^2 + s*t - t)*x - e6*e5;
	Grst_tilde := Grst - 2*t;
	Frsti_tilde := Coefficients(-3*(Delta*Grst_tilde^2 + 4*s*t*Hrst_tilde^3));
	h0 := Frsti_tilde[1]; h1 := Frsti_tilde[2]; h2 := Frsti_tilde[3]; h3 := Frsti_tilde[4]; h4 := Frsti_tilde[5]; h5 := Frsti_tilde[6]; h6 := Frsti_tilde[7];

	a0 := 0; a1 := 0; a2 := 0; a3 := Delta;
	b0 := 0; b1 := 0; b2 := Delta; b3 := 0;
	c0 := 0; c1 := Delta; c2 := 0; c3 := 0;
	a4 := f6D - h6;
	c9 := f0D - h0;
	a5 := (f5D - h5)*INV3;
	b4 := -a5;
	c8 := (f1D - h1)*INV3;
	b9 := -c8;
	b5 := 4*e1*( Delta*( 5*e2 - e1*e4^2 - 2*(e2*e3*e5 - e6)) + e2*(e3*e5)^2*e6*(12*e5 + 9) );
	a7 := 4*e1*(Delta*(e2 + e1*e4^2) - e2*(e3*e5)^2*e6*(3*e5 + 2));
	c4 := b5 + (f4D - h4)*INV3;
	a6 := 2*b5 - c4 - 4*a7 + (f4D - h4);
	a8 := 12*e1* ( e1*( e6^3*( e5*(e4*e5 + e3) + e1*e3^2) - (e2*e3*e5)^2*e3*e4) + e2*(Delta + e2*e3*(e3*e5)^2));
	b7 := -4*e1* ( e2*( e5*( e3*e6*( e1*e3*e6*(-5*e5 - 4) - e4*e5^2) + 3*e4*Delta - 2*e4*(e4*e5)^2) - e2*Delta) + e1*e4^3*Delta);
	c5 := a8;
	b6 := 4*(a8 - b7) - (f3D - h3);
	b8 := 4*e1*( Delta*( e1*( e6*( e6 -2*e4^2) - e2^2*(e3^2  - 5*e4)) + e2*(e6 - 5*e2*e5 + 2*e4)) - e2*e3*(e5*e6)^2*(12*e5 + 9));
	c7 := 4*e1* (Delta* ( e2*( e1*e4^2 + e6 + e2) + e1*e4^2*e6) + e2*e3*(e5*e6)^2*(2*e1*e4 + e5));
	a9 := b8 + (f2D - h2)*INV3;
	c6 := 2*b8 - a9 - 4*c7 + (f2D - h2);
	
	a10 := (a4*b5 + f6D*(a6 - b5) - a5*(2*f5D + h5)*INV3 )*invD;
	c19 := (c9*b8 + f0D*(c6 - b8) - c8*(2*f1D + h1)*INV3 )*invD;
	a11 := (2*f6D*(b6 + 2*(c5 - b7)) + f5D*(a6 - a7 - c4) + 3*a4*b7 - h5*a7 )*invD;
	c18 := (2*f0D*(b6 + 2*(a8 - b7)) + f1D*(c6 - c7 - a9) + 3*c9*b7 - h1*c7 )*invD;
	b10 := (b4*c4 + 4*f6D*b7 - 4*h6*a8 + a7*(9*a5 + 4*h5) - 3*a4*(a8 + b7) )*invD*INV2;
	b19 := (b9*a9 + 4*f0D*b7 - 4*h0*c5 + c7*(9*c8 + 4*h1) - 3*c9*(c5 + b7) )*invD*INV2;
	a13 := (f6D*(10*a9 - 9*c6 - b8)*INV2 - h5*b7 - 3*b5*a7 + f5D*c5 )*invD;
	c17 := (f0D*(10*c4 - 9*a6 - b5)*INV2 - h1*b7 - 3*b8*c7 + f1D*a8 )*invD;
	b11 := (a4*(2*c7 - c6) + c4*(2*b5 - c4) + f6D*(4*b8 - 3*c6) + h6*(b8 - 2*a9) + 2*f5D*(a8 - b7) + a7*(2*a6 - a7) - 6*a13*Delta )*invD*INV4;
	b18 := (c9*(2*a7 - a6) + a9*(2*b8 - a9) + f0D*(4*b5 - 3*a6) + h0*(b5 - 2*c4) + 2*f1D*(c5 - b7) + c7*(2*c6 - c7) - 6*c17*Delta )*invD*INV4;
	a12 := (8*(2*f2D*a4 - a13*Delta + 12*h6*c7) + a5*(9*b6 - 7*f3D) - a5*(h3 - 32*a8) + 2*a7*(6*c4 - b5) - 2*a6*(2*c4 - 4*a6 + 11*a7) + 115*b6*(h6 - f6D + a4)*INV16 )*invD*INV16;
	c15 := (8*(2*f4D*c9 - c17*Delta + 12*h0*a7) + c8*(9*b6 - 7*f3D) - c8*(h3 - 32*c5) + 2*c7*(6*a9 - b8) - 2*c6*(2*a9 - 4*c6 + 11*c7) + 115*b6*(h0 - f0D + c9)*INV16 )*invD*INV16;
	c10 := (c7*(3*f6D + 5*h6 - a4) + c4^2 + 2*a5*a8 - a7*(2*a6 - a7) )*invD*INV4;
	a19 := (a7*(3*f0D + 5*h0 - c9) + a9^2 + 2*c8*c5 - c7*(2*c6 - c7) )*invD*INV4;
	a16 := (a7*(3*a8 + b7 - 2*f3D - b6) + c8*(3*f6D + h6) + a5*b8 - c7*(3*f5D + h5) + b5*a8 - a6*b7 )*invD*INV4;
	c16 := (c7*(3*c5 + b7 - 2*f3D - b6) + a5*(3*f0D + h0) + c8*b5 - a7*(3*f1D + h1) + b8*c5 - c6*b7 )*invD*INV4;
	b13 := (2*a7*(2*(f3D + b6) + h3 + a8 - b7) + 2*b5*(b7 + a8) - c4*(b7 + a8) - f5D*(3*a9 - 2*c6) + h5*(2*b8 - a9) - 4*f6D*c8 - 3*a5*c7 )*invD*INV4;
	b17 := (2*c7*(2*(f3D + b6) + h3 + c5 - b7) + 2*b8*(b7 + c5) - a9*(b7 + c5) - f1D*(3*c4 - 2*a6) + h1*(2*b5 - c4) - 4*f0D*a5 - 3*c8*a7 )*invD*INV4;
	a14 := (c8*(10*f6D - 3*a4) + b13*Delta - h5*(b8 + c6)*INV2 + f5D*(2*b8 - a9) - a7*(7*f3D - 6*a8) + 2*f4D*(a8 - b7) )*invD;
	c14 := (a5*(10*f0D - 3*c9) + b17*Delta - h1*(b5 + a6)*INV2 + f1D*(2*b5 - c4) - c7*(7*f3D - 6*c5) + 2*f2D*(c5 - b7) )*invD;
	c11 := (3*(c4*b7 + a7*a8)*INV2 - Delta*(2*b13 + 9*a16) + 4*(f5D*c7 - f6D*c8) )*invD;
	a18 := (3*(a9*b7 + c7*c5)*INV2 - Delta*(2*b17 + 9*c16) + 4*(f1D*a7 - f0D*a5) )*invD;
	b12 := ((b6*(c4 - a7) + a6*(a8 + b7))*INV2 + Delta*(b13 - a14 + 6*a16) - c4*b7 - a7*a8 )*invD;
	b15 := ((b6*(a9 - c7) + c6*(c5 + b7))*INV2 + Delta*(b17 - c14 + 6*c16) - a9*b7 - c7*c5 )*invD;
	b16 := (c7*(6*f4D + 2*h4 - a6 + a7) + 2*b5*(b8 - a9) + c9*(3*h6 - 7*f6D) + b7*(b7 - 2*b6) - 4*h0*a4 + a5*c8 - c6*a7 )*invD*INV4;
	c13 := (c8*(a5 + 3*f5D + h5) - c9*(3*(h6 + a4) + 5*f6D) + b5*(b8 + 2*c7 - c6) + b7*(b7 - 2*b6) + a8^2 )*invD*INV4 - b16;
	a17 := (a5*(c8 + 3*f1D + h1) - a4*(3*(h0 + c9) + 5*f0D) + b8*(b5 + 2*a7 - a6) + b7*(b7 - 2*b6) + c5^2 )*invD*INV4 - b16;
	a15 := ((a6*(f2D - 5*c7  + b8 - h2) + a8*(a8 - b7 + 2*b6))*INV2 - a7*(5*f2D + 3*(c7 - b8) + h2)*INV3 + 2*c9*(3*f6D + h6) - (c8*(f5D + h5) - h1*a5) )*invD;
	c12 := ((c6*(f4D - 5*a7  + b5 - h4) + c5*(c5 - b7 + 2*b6))*INV2 - c7*(5*f4D + 3*(a7 - b5) + h4)*INV3 + 2*a4*(3*f0D + h0) - (a5*(f1D + h1) - h5*c8) )*invD;
	b14 := (2*(2*(f4D*c7 - f5D*c8 - f6D*c9) - h0*a4 - a5*c8 - f3D*b7 - c4*a9) - 3*h1*a5 + b8*(b5 + c4) + a8*(f3D + h3) )*invD + 4*(c13 - b16) + c12;

	d0 := Delta^3;
	d1 := Delta*j2;
	d2 := Delta*j1;
	d3 := Delta*j0;
	d9 := Delta*( 2*(f0D*b5 - h4*c9) + c8*(f3D - 4*a8) + Delta*(4*c17 + c15) - j2fac*(108*c9 + 72*h0) + 4*f2D*c7);
	d4 := Delta*( 2*(f6D*b8 - h2*a4) + a5*(f3D - 4*c5) + Delta*(4*a13 + a12) - j0fac*(108*a4 + 72*h6) + 4*f4D*a7);
	d8 := Delta*( Delta*(4*c16 + c14) + b5*(h1 - f1D)*INV3 + 2*(f3D*c7 - 2*h0*a5 - f5D*c9));
	d5 := Delta*( Delta*(4*a16 + a14) + b8*(h5 - f5D)*INV3 + 2*(f3D*a7 - 2*h6*c8 - f1D*a4));
	d6 := Delta*( a8*(18144*c7 + 1344*(h2 - f2D) - 2016*b8  + 1386*h3 + 3198*f3D - 1770*b6)  + j0fac*(51840*h3 - 77760*b6 - 194400*b7 + 303264*c4 - 17712*b5 - 478656*f4D) + c6*(3888*b6 - 2592*h3 + 9720*b7 + 12528*f4D + 4644*b5 - 10584*c4) + b7*(6006*b6 - 678*h3 - 4890*f3D) + f1D*(1728*a6 - 8640*a7 - 1024*h5) + h1*(1296*a6 - 25920*j2fac - 22464*a5) + b6*(192*b6 + 384*f3D) + f2D*(4608*f4D - 512*h4) - f0D*(24384*h6 + 11904*f6D) + c8*(22768*h5 - 2416*f5D) - a9*(240*b5 + 1536*h4)+ 5664*b16*Delta + 49248*h0*a4 - 45600*h6*c9 - 1536*f3D^2 )*INV216;
	d7 := Delta*( a8*(336*(f2D - h2) - 4536*c7 + 504*b8 - 822*f3D - 378*h3 + 474*b6) + j0fac*(19440*b6 - 12960*h3 + 48600*b7 - 71928*c4 + 119664*f4D + 3780*b5) + c6*(2646*c4 - 972*b6 + 648*h3 - 2430*b7 - 1161*b5 - 3132*f4D) + f3D*(384*f3D + 1299*b7 - 96*b6) + h1*(5616*a5 - 324*a6 + 6480*j2fac) + f1D*(256*h5 - 432*a6 + 2160*a7) + f0D*(2904*f6D + 6312*h6) + a9*(384*h4 - 12*b5) + f2D*(128*h4 - 1152*f4D) + b7*(165*h3 - 1461*b6) + c8*(592*f5D - 5680*h5) - 48*b6^2  - 1272*b16*Delta - 12312*h0*a4 + 11184*h6*c9)*INV216;
	d10 := (a5*(f3D*(161280*c4 - 30720*f4D - 145920*a6 + 2343345*a7) + a5*(1488420*a9 - 3587400*b8 + 322560*f2D) - f4D*(30720*b6  + 199680*a8 + 284160*b7) + a7*(5539185*b6 + 691191*h3) + f5D*(510720*b8 - 7074540*c7) - 15360*f1D*h6 + 996480*b5*b7 + 10958040*a16*Delta  + 866880*c4*a8  + 1586340*h5*c7) + f5D*(f5D*(130560*b8 + 2453760*c7 - 215040*a9) + c4*(158400*b7 - 2588160*a8 - 11520*f3D) - a7*(680388*f3D + 2668740*b6 + 191292*h3) + f4D*(61440*a8 - 46080*b7) - 2780160*a16*Delta - 384000*b5*b7 + 7680*a6*b6 + 161280*f6D*c8) + a7*(h6*(69892224*a9- 131227776*c7- 33135744*c6 - 3661632*f2D) + c4*(4174608*b5 + 3304896*c4 - 2843904*f4D) + b5*(129696*b5 + 2325504*f4D) + f6D*(74365920*c7 - 13811968*f2D - 20964800*h2) - Delta*(2124480*a12 + 2182800*a13) + 34296960*a4*b8) + f6D*(a8*(552960*b6 - 2407680*b7 + 2313600*a8) + a6*(18504000*c7 - 46080*f2D + 568320*b8 + 9398400*a9) + c7*(35443200*h4 - 59031360*b5) + c4*(138240*f2D - 8559360*a9)) + c4*(a6*(15360*f4D + 81600*c4 - 76800*b5) + 2525760*h5*b7 - 184320*a12*Delta- 1411200*h6*b8  - 1558080*a4*c7) + h6*(b7*(1075200*f3D - 122880*b6 - 439680*b7) + 34560*a4*c9 - 15360*h3^2 - 764160*a6*c7) - a4*(a8*(608640*a8 - 2079360*b7) + 702720*a6*b8) + a6*Delta*(84480*a12 + 1265280*a13) )*INV103680 + (j0*a10 + j1*b10 + j2*c10);
	d11 := (a7*(f5D*(663936*f2D+ 331980*c7 + 2228928*a9 - 3106272*c6) + f3D*(1445873*a6 - 1920672*c4  - 881400*a7) + a5*(5212692*b8- 3170316*f2D - 2121108*h2) + a8*(2798016*f4D - 1217892*c4 + 74932*b5) + a6*(480831*h3  - 49647*b6) + b7*(3974724*c4- 3129984*f4D) - a7*(241176*b6 + 1537536*h3) - 165984*h1*a4  + 8144136*a16*Delta  + 4161756*h5*c7) + b7*(b5*(284544*h4- 480168*b5 + 441064*a6) + f5D*(160056*b7 - 35568*h3 + 326040*a8) + h5*(118560*h3 - 17784*b6 - 569088*b7) + a4*(480168*a9 - 960336*f2D) + a6*(102960*f4D - 400556*c4) + 47424*h2*h6 - 1421732*a5*a8) + a5*(a8*(158080*b6 + 670852*a8 + 98800*h3) + h4*(8208*f2D + 24624*a9 - 24624*c6) + a6*(372576*c7 - 3496*b8) - c8*(160056*f5D + 88920*h5) - 332424*b5*c6 + 213408*h6*c9) + a8*(h6*(397176*a9 - 219336*c6 - 136344*f2D) - Delta*(725192*a13 + 158080*a12) + a4*(201552*b8 + 21736*h2) - 148200*f6D*h2) + a6*(h6*(253344*f1D - 747136*c8) + Delta*(56992*a14 + 3320512*a16) - f5D*(39624*b8 + 499408*c7) + 196352*h1*a4) + f5D*(189696*h0*h6 + h1*(71136*h5 - 82992*f5D) - 2736*h2*h4) - h5*(195624*b5*b8 - 11856*h1*h5 - 2736*h2*h4) + a16*Delta*(1849536*f4D - 5975424*c4) + 640224*f1D*f6D*b5)*INV213408 + (j0*a11 + j1*b11 + j2*c11);
	d12 := (a7*(a8*(71688639263904*b6 - 47633590083456*h3  + 8226721831536*a8 + 150071629876272*b7) + f2D*(726002896320*b5 - 179138718720*h4 + 138945245672016*a6 + 3086073952448*a7) + a6*(53546718093024*b8 - 151947714850584*a9 + 325475748300312*c7) + h4*(52749740160*a9 - 29732886144*c6 + 588120892416*c7) + a7*(6586890862080*b8 - 4249353171776*h2 - 118179243959904*c7) + b7*(11182445707680*f3D - 2820326389920*b7) + h5*(20027432146176*c8 - 8088690876864*f1D) - b5*(224586788400*a9 + 111193712928*c6) - 14100621058368*f5D*c8 - 18611697184704*h1*a5) + a6*(a8*(6525676207557*h3 - 22601221319781*f3D - 10603550635821*b6 + 80301151266336*a8) + a6*(13243726386768*c6 - 14700419646732*a9 - 11815674624*f2D + 15956038353324*c7) + h4*(4508524800*a9 + 1596351744*c6 - 2344823770176*c7) + b5*(8408066073336*c6 - 24346033920*f2D - 4030968240*a9) + b7*(55566725760*f3D - 273511527120*b7) + h5*(14260256617152*f1D - 30843403202664*c8) - 12028028084280*a15*Delta + 12154510984824*f5D*c8 + 28183820804568*h1*a5) + a8*(h5*(26468641652544*c7 + 23504123448*f2D + 24429383784*a9 - 5375754349992*c6) + f5D*(108746474616*a9 - 83614417848*f2D - 131580175896*c6) + f4D*(14126711040*b6 + 871146327168*b7) + a8*(32077009590912*h4 - 72100886590512*b5) + c4*(27577143360*h3 - 1117106909568*b7) +31709957760*f3D*h4 - 116319939840*f1D*a4 + 66604982184*h2*a5) + b7*(a5*(458399616012*f2D - 4438398297996*a9 + 2342796395004*c6) + f5D*(26218297404*h2 - 424505659968*f2D) + h5*(322851453444*h2 - 256082141952*b8) + b7*(844880615280*b5 - 500669994240*h4) + 8115344640*h1*a4 + 12336736557600*a16*Delta) + a9*(f6D*(230723116416*c6 - 4057672320*a9 - 86563676160*f2D) - 37729916640*a4*c7) + c7*(26149443840*h5*b6 - 866538466560*h4*c4 + 731141831160*b5^2 + 37504321920*f2D*a4) + f5D*(b5*(53989584480*c8  - 13826142720*f1D) + 10369607040*f4D*c8 + 13525574400*f3D*c6) - c6*(106107356160*f2D*f6D + 24556431744*h6*b8) + h4*(1352557440*a15*Delta - 1352557440*a4*c9) + h1*(5184803520*c4*a5  - 2404546560*h3*h6) + 36519050880*a4*a19*Delta - 601136640*f0D*h5^2)*INV8115344640 + (j0*a12 + j1*b12 + j2*c12);
	d13 := (a6*(a8*(152377957017*f3D - 43858328553*h3 - 542547965232*a8 + 70926086673*b6) + a7*(1027033984428*a9 - 939329740800*f2D - 364246057056*b8 - 2221420681944*c7) + a6*(99362564352*a9 - 72671040*f2D - 89555386368*c6 - 110375191650*c7) + b5*(218013120*f2D - 56749284936*c6  + 235471860*a9) + h4*(16654460832*c7 - 290684160*a9 + 266460480*c6) + h5*(208629280080*c8 - 96846091680*f1D) + b7*(2716672608*b7 - 2100591792*f3D) + 49052952*a4*c9 + 81476094024*a15*Delta - 81917937036*f5D*c8 - 190688851080*h1*a5) + a7*(a8*(324608223888*h3 - 485859058776*b6 - 49610165904*a8 - 1024182914976*b7) + h4*(2131683840*f2D - 2241445536*c7- 1731993120*c6 - 654039360*a9) + a7*(35892961856*h2 - 55359277320*b8 - 22401676160*f2D + 792582864408*c7) + b5*(3475392804*a9 - 3804328944*f2D + 2869454808*c6) + b7*(23841196236*b7 - 75249410184*f3D) + c8*(93792832848*f5D - 134772145560*h5)+ 124109677224*h1*a5 + 55935056112*f1D*h5) + a8*(h5*(37133566470*c6 - 117723554*f2D - 1120252614*a9 - 176536537632*c7) + f5D*(2268786338*f2D + 2892135402*c6 - 4942122042*a9) + c4*(196817400*h3 + 5019607476*b7) + a8*(490324404960*b5 - 218074296960*h4) - f4D*(3527778384*b7 + 24223680*b6) - 133230240*f3D*h4  + 245264760*f1D*a4 - 450065382*h2*a5) + b7*(a5*(28009741032*a9 - 3964646088*f2D - 17342227656*c6) + h5*(1181516544*b8 - 1946519640*h2) + b7*(4266587520*h4 - 7199866440*b5) + f5D*(4678872120*f2D - 319673952*h2) + 370622304*h1*a4) + c7*(327019680*h5*b6 + 218013120*h4*c4 + a4*(2411681688*a9 - 1183058136*c6) - 183948570*b5^2) + f6D*c6*(4113978336*a9 - 544763232*c6 - 1177270848*f2D) + f5D*(436026240*f1D*b5 - 13625820*b5*c8 - 690374880*f4D*c8) + Delta*(218013120*h2*a13- 109006560*h4*a15 - 85899528000*b7*a16) + h1*(96894720*h3*h6 - 136258200*c4*a5) + 109006560*h4*a4*c9 + 290684160*f0D*h5^2 - 2943177120*f6D*a9^2) *INV327019680 + (j0*a13 + j1*b13 + j2*c13);
	d14 := (a7*(f3D*(1609023*c7 - 680238*a9 + 952359*c6 - 331056*f2D) + b6*(1197666*a9 - 335088*f2D - 3120369*c7 - 360885*c6) + f1D*(1352928*c4 - 1327680*b5 + 144384*f4D) + h3*(333360*f2D - 293499*c7 - 6489*b8) + c8*(1074888*c4 - 2640096*f4D + 30024*b5) + h5*(2385984*c9 - 932928*f0D)+ 357120*a18*Delta - 6584256*h0*a5 - 537168*f5D*c9) + b7*(b7*(378*b6 - 630*f3D - 42*h3) + b8*(87876*h4 - 61092*f4D - 148056*b5) + c7*(397776*c4 - 109248*b5 - 747360*f4D) + a9*(35136*f4D + 31704*c4) + a8*(1680*b6 + 3552*f3D) + c8*(78288*f5D - 228888*a5) + 2592*a4*c9 + 8640*a15*Delta - 27984*f1D*a5) + c7*(f5D*(1445940*c7 - 535440*b8 - 82176*f2D) + a6*(8448*f3D + 40272*b6) + a8*(161568*f4D - 125064*c4) - a5*(12684*a9 + 124128*f2D) - 7776*h6*c8  - 5935032*a16*Delta - 286332*h5*c7) + b8*(a8*(6300*c4 + 101844*b5 - 61920*f4D) + a5*(563760*a9 - 148686*c6 - 4032*f2D) + f5D*(44352*a9 - 195646*b8) - 108*a4*c8 + 151294*h5*b8) + a5*(2196*h0*a6 + c9*(2268*b5 - 864*f4D) - 3456*b6*c8 + 2880*f1D*h3 + a8*(159816*c8 - 72768*f1D) - 321216*a19*Delta) + Delta*(3456*c8*a12 + a16*(1410048*a9 - 902736*c6 + 176256*f2D) + 8064*a6*a18 - 2880*a8*a15) + a6*(f5D*(54356*f0D - 8496*h0) - 45860*f0D*h5) + c9*(3168*h6*a8 - 432*h3*a4)- 2880*f3D*a8^2)*INV864 + (j0*a14 + j1*b14 + j2*c14);
	d15 := (c7*(c5*(71688639263904*b6 - 47633590083456*h3  + 8226721831536*c5 + 150071629876272*b7) + f4D*(726002896320*b8 - 179138718720*h2 + 138945245672016*c6 + 3086073952448*c7) + c6*(53546718093024*b5 - 151947714850584*c4 + 325475748300312*a7) + h2*(52749740160*c4 - 29732886144*a6 + 588120892416*a7) + c7*(6586890862080*b5 - 4249353171776*h4 - 118179243959904*a7) + b7*(11182445707680*f3D - 2820326389920*b7) + h1*(20027432146176*a5 - 8088690876864*f5D) - b8*(224586788400*c4 + 111193712928*a6) - 14100621058368*f1D*a5 - 18611697184704*h5*c8) + c6*(c5*(6525676207557*h3 - 22601221319781*f3D - 10603550635821*b6 + 80301151266336*c5) + c6*(13243726386768*a6 - 14700419646732*c4 - 11815674624*f4D + 15956038353324*a7) + h2*(4508524800*c4 + 1596351744*a6 - 2344823770176*a7) + b8*(8408066073336*a6 - 24346033920*f4D - 4030968240*c4) + b7*(55566725760*f3D - 273511527120*b7) + h1*(14260256617152*f5D - 30843403202664*a5) - 12028028084280*c12*Delta + 12154510984824*f1D*a5 + 28183820804568*h5*c8) + c5*(h1*(26468641652544*a7 + 23504123448*f4D + 24429383784*c4 - 5375754349992*a6) + f1D*(108746474616*c4 - 83614417848*f4D - 131580175896*a6) + f2D*(14126711040*b6 + 871146327168*b7) + c5*(32077009590912*h2 - 72100886590512*b8) + a9*(27577143360*h3 - 1117106909568*b7) +31709957760*f3D*h2 - 116319939840*f5D*c9 + 66604982184*h4*c8) + b7*(c8*(458399616012*f4D - 4438398297996*c4 + 2342796395004*a6) + f1D*(26218297404*h4 - 424505659968*f4D) + h1*(322851453444*h4 - 256082141952*b5) + b7*(844880615280*b8 - 500669994240*h2) + 8115344640*h5*c9 + 12336736557600*c16*Delta) + c4*(f0D*(230723116416*a6 - 4057672320*c4 - 86563676160*f4D) - 37729916640*c9*a7) + a7*(26149443840*h1*b6 - 866538466560*h2*a9 + 731141831160*b8^2 + 37504321920*f4D*c9) + f1D*(b8*(53989584480*a5  - 13826142720*f5D) + 10369607040*f2D*a5 + 13525574400*f3D*a6) - a6*(106107356160*f4D*f0D + 24556431744*h0*b5) + h2*(1352557440*c12*Delta - 1352557440*c9*a4) + h5*(5184803520*a9*c8  - 2404546560*h3*h0) + 36519050880*c9*c10*Delta - 601136640*f6D*h1^2)*INV8115344640 + (j0*a15 + j1*b15 + j2*c15);
	d16 := (b7*(f4D*(28021592352*c7 - 1186872960*a9 - 90215424*f2D + 2564727256*b8) + b7*(11080992*h3 - 61233120*f3D + 36739872*b6) + c4*(15634944*f2D - 2143884288*a9 - 13429047840*c7) + f1D*(468525408*a5 - 31277376*f5D) + b8*(5647063032*b5  - 3255914584*h4) + c8*(8596985904*a5 - 2837594448*f5D) + a8*(18118464*f3D - 18670080*b6) + 4315057968*b5*c7 + 12224160*a15*Delta) + a7*(f3D*(10870942872*f2D - 49034471628*c7 + 21659664474*a9 - 31509056853*c6) + b6*(11004658584*f2D - 43666946766*a9 + 111387259092*c7 + 13921300635*c6) + f1D*(44079092448*b5 - 5433312768*f4D - 46842869568*c4) + h3*(187974099*b8 + 10704948264*c7 - 11120962200*f2D) + c8*(90357626208*f4D - 1937626536*b5 - 37449463512*c4) + c9*(24032217992*f5D - 86657028776*h5) + 237813785376*h0*a5  + 38797324800*f0D*h5 - 9889831872*a18*Delta) + b8*(f5D*(18592956792*c7- 1205128704*a9 - 12300288*f2D + 6491862111*b8) + a8*(1950122304*f4D + 192529896*c4 - 3659704464*b5) + a5*(59754240*f2D - 17589284478*a9 + 3699429813*c6) + a6*(8948160*b6 + 14092416*f3D) - 5222075775*h5*b8 ) + c7*(a5*(4309388928*f2D - 1812003696*a9) + f5D*(2948345088*f2D - 45120978720*c7) + a8*(4260518496*c4 - 5260253856*f4D) - a6*(346663200*f3D + 1408667520*b6) + 7915475520*h5*c7 + 211025095584*a16*Delta) + Delta*(a16*(35150202888*c6 - 5556385536*f2D - 56712723408*a9) + a19*(11345435712*a5 - 299120640*f5D) + 13837824*c9*a11 - 170775072*a6*a18 + 16320096*a8*a15 + 12300288*h2*a14) + h3*(h3*(3234816*b6 - 1078272*h3) - 741312*a4*c9 - 2426112*b6^2 + h4*(4313088*a9 - 1078272*c6 + 1437696*f2D)) + a6*(9424896*f4D*h1 + h0*(303996576*f5D - 58496256*a5) + f0D*(1627032160*h5 - 1976850304*f5D)) + b6*(h4*(1617408*c6 - 6469632*a9 - 2156544*f2D) + 5189184*a4*c9) + a8*(43041024*f3D*a8 + a5*(3190273008*f1D - 5827652064*c8)) + h1*h6*(18450432*a9 - 22843392*c6) - 8154432*f3D*a4*c9)*INV13837824 + (j0*a16 + j1*b16 + j2*c16);
	d17 := (c6*(c5*(152377957017*f3D - 43858328553*h3 - 542547965232*c5 + 70926086673*b6) + c7*(1027033984428*c4 - 939329740800*f4D - 364246057056*b5 - 2221420681944*a7) + c6*(99362564352*c4 - 72671040*f4D - 89555386368*a6 - 110375191650*a7) + b8*(218013120*f4D - 56749284936*a6  + 235471860*c4) + h2*(16654460832*a7 - 290684160*c4 + 266460480*a6) + h1*(208629280080*a5 - 96846091680*f5D) + b7*(2716672608*b7 - 2100591792*f3D) + 49052952*c9*a4 + 81476094024*c12*Delta - 81917937036*f1D*a5 - 190688851080*h5*c8) + c7*(c5*(324608223888*h3 - 485859058776*b6 - 49610165904*c5 - 1024182914976*b7) + h2*(2131683840*f4D - 2241445536*a7- 1731993120*a6 - 654039360*c4) + c7*(35892961856*h4 - 55359277320*b5 - 22401676160*f4D + 792582864408*a7) + b8*(3475392804*c4 - 3804328944*f4D + 2869454808*a6) + b7*(23841196236*b7 - 75249410184*f3D) + a5*(93792832848*f1D - 134772145560*h1)+ 124109677224*h5*c8 + 55935056112*f5D*h1) + c5*(h1*(37133566470*a6 - 117723554*f4D - 1120252614*c4 - 176536537632*a7) + f1D*(2268786338*f4D + 2892135402*a6 - 4942122042*c4) + a9*(196817400*h3 + 5019607476*b7) + c5*(490324404960*b8 - 218074296960*h2) - f2D*(3527778384*b7 + 24223680*b6) - 133230240*f3D*h2  + 245264760*f5D*c9 - 450065382*h4*c8) + b7*(c8*(28009741032*c4 - 3964646088*f4D - 17342227656*a6) + h1*(1181516544*b5 - 1946519640*h4) + b7*(4266587520*h2 - 7199866440*b8) + f1D*(4678872120*f4D - 319673952*h4) + 370622304*h5*c9) + a7*(327019680*h1*b6 + 218013120*h2*a9 + c9*(2411681688*c4 - 1183058136*a6) - 183948570*b8^2) + f0D*a6*(4113978336*c4 - 544763232*a6 - 1177270848*f4D) + f1D*(436026240*f5D*b8 - 13625820*b8*a5 - 690374880*f2D*a5) + Delta*(218013120*h4*c17- 109006560*h2*c12 - 85899528000*b7*c16) + h5*(96894720*h3*h0 - 136258200*a9*c8) + 109006560*h2*c9*a4 + 290684160*f6D*h1^2 - 2943177120*f0D*c4^2)*INV327019680 + (j0*a17 + j1*b17 + j2*c17);
	d18 := (c7*(f1D*(663936*f4D+ 331980*a7 + 2228928*c4 - 3106272*a6) + f3D*(1445873*c6 - 1920672*a9  - 881400*c7) + c8*(5212692*b5- 3170316*f4D - 2121108*h4) + c5*(2798016*f2D - 1217892*a9 + 74932*b8) + c6*(480831*h3  - 49647*b6) + b7*(3974724*a9- 3129984*f2D) - c7*(241176*b6 + 1537536*h3) - 165984*h5*c9  + 8144136*c16*Delta  + 4161756*h1*a7) + b7*(b8*(284544*h2- 480168*b8 + 441064*c6) + f1D*(160056*b7 - 35568*h3 + 326040*c5) + h1*(118560*h3 - 17784*b6 - 569088*b7) + c9*(480168*c4 - 960336*f4D) + c6*(102960*f2D - 400556*a9) + 47424*h4*h0 - 1421732*c8*c5) + c8*(c5*(158080*b6 + 670852*c5 + 98800*h3) + h2*(8208*f4D + 24624*c4 - 24624*a6) + c6*(372576*a7 - 3496*b5) - a5*(160056*f1D + 88920*h1) - 332424*b8*a6 + 213408*h0*a4) + c5*(h0*(397176*c4 - 219336*a6 - 136344*f4D) - Delta*(725192*c17 + 158080*c15) + c9*(201552*b5 + 21736*h4) - 148200*f0D*h4) + c6*(h0*(253344*f5D - 747136*a5) + Delta*(56992*c14 + 3320512*c16) - f1D*(39624*b5 + 499408*a7) + 196352*h5*c9) + f1D*(189696*h6*h0 + h5*(71136*h1 - 82992*f1D) - 2736*h4*h2) - h1*(195624*b8*b5 - 11856*h5*h1 - 2736*h4*h2) + c16*Delta*(1849536*f2D - 5975424*a9) + 640224*f5D*f0D*b8)*INV213408 + (j0*a18 + j1*b18 + j2*c18);
	d19 := (c8*(f3D*(161280*a9 - 30720*f2D - 145920*c6 + 2343345*c7) + c8*(1488420*c4 - 3587400*b5 + 322560*f4D) - f2D*(30720*b6  + 199680*c5 + 284160*b7) + c7*(5539185*b6 + 691191*h3) + f1D*(510720*b5 - 7074540*a7) - 15360*f5D*h0 + 996480*b8*b7 + 10958040*c16*Delta  + 866880*a9*c5  + 1586340*h1*a7) + f1D*(f1D*(130560*b5 + 2453760*a7 - 215040*c4) + a9*(158400*b7 - 2588160*c5 - 11520*f3D) - c7*(680388*f3D + 2668740*b6 + 191292*h3) + f2D*(61440*c5 - 46080*b7) - 2780160*c16*Delta - 384000*b8*b7 + 7680*c6*b6 + 161280*f0D*a5) + c7*(h0*(69892224*c4- 131227776*a7- 33135744*a6 - 3661632*f4D) + a9*(4174608*b8 + 3304896*a9 - 2843904*f2D) + b8*(129696*b8 + 2325504*f2D) + f0D*(74365920*a7 - 13811968*f4D - 20964800*h4) - Delta*(2124480*c15 + 2182800*c17) + 34296960*c9*b5) + f0D*(c5*(552960*b6 - 2407680*b7 + 2313600*c5) + c6*(18504000*a7 - 46080*f4D + 568320*b5 + 9398400*c4) + a7*(35443200*h2 - 59031360*b8) + a9*(138240*f4D - 8559360*c4)) + a9*(c6*(15360*f2D + 81600*a9 - 76800*b8) + 2525760*h1*b7 - 184320*c15*Delta- 1411200*h0*b5  - 1558080*c9*a7) + h0*(b7*(1075200*f3D - 122880*b6 - 439680*b7) + 34560*c9*a4 - 15360*h3^2 - 764160*c6*a7) - c9*(c5*(608640*c5 - 2079360*b7) + 702720*c6*b5) + c6*Delta*(84480*c15 + 1265280*c17) )*INV103680 + (j0*a19 + j1*b19 + j2*c19);

	ai := [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19];
	bi := [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19];
	ci := [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19];
	di := [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19];

	return [ai,bi,ci,di], [j0,j1,j2,Delta^2];

end function;


function get_codomain_curve_polynomial(rst)

	r,s,t := Explode(rst);
	Kx<x> := PolynomialRing(Parent(r));

	e1 := s;
	e2 := t;
	e3 := r - 1;
	e4 := r - t;
	e5 := r*s - s*t - 1;
	e6 := r^2 - t;
	Delta := (e1*e3*e6)^2 + e5*(e3*e6*(e1*e4 + e5) + e4^2*e5);

	Gco := Delta*( (s - s*t - 1)*x^3 + 3*s*e4*x^2 + 3*r*s*e4*x + r^3*s - s*t^2 - t );
	Hco := e3*e5*x^2 + (r^3*s - 2*r^2*s + r*s*t + r - s*t^2 + s*t - t)*x - e5*e6;
	lambdaco := 4*Delta*s*t;
	
	Fco := Gco^2 + lambdaco*Hco^3;
	
	return -3*Fco;
end function;


function BFT_evaluation(kernel, points, other_points)
	/*
	Input: a (3,3)-subgroup kernel of a Jacobian (not in BFT parametrization), and auxiliary points (on the Kummer) to evaluate the isogeny at
	Output: a new Jacobian J (not in BFT parametrization), as well as the images of the auxiliary points under the isogeny
	*/
	J := Parent(kernel[1]);
	C := Curve(J);
	f := HyperellipticPolynomials(C);
	rst, transform := get_rst_transform(kernel);
	a,b,c,d,e := Explode(transform);
	transform_points := apply_transformation([d,-b,-c,a,1/e^2], points, f, rst);
	transform_other_points := apply_transformation([d,-b,-c,a,1/e^2], other_points, f, rst);
	fnew := get_codomain_curve_polynomial(rst);
	Cnew := HyperellipticCurve(fnew);
	Jnew := Jacobian(Cnew);
	Knew := KummerSurface(Jnew);
	ai, bi, ci, di := Explode(get_codomain_Kummer_coefficients(rst));
	codomain_points := [];
	for pt in transform_points do
		k0, k1, k2, k3 := Explode(Eltseq(pt));
		ki := [k3^3, k2*k3^2, k1*k3^2, k0*k3^2, k2^2*k3, k1*k2*k3, k0*k2*k3, k1^2*k3, k0*k1*k3, k0^2*k3,
			k2^3, k1*k2^2, k0*k2^2, k1^2*k2, k0*k1*k2, k0^2*k2, k1^3, k0*k1^2, k0^2*k1, k0^3];
		xi0 := &+[ai[j]*ki[j] : j in [1..#ki]];
		xi1 := &+[bi[j]*ki[j] : j in [1..#ki]];
		xi2 := &+[ci[j]*ki[j] : j in [1..#ki]];
		xi3 := &+[di[j]*ki[j] : j in [1..#ki]];
		Append(~codomain_points, Knew ! [xi0,xi1,xi2,xi3]);
	end for;
	codomain_other_points := [];
	for pt in transform_other_points do
		k0, k1, k2, k3 := Explode(Eltseq(pt));
		ki := [k3^3, k2*k3^2, k1*k3^2, k0*k3^2, k2^2*k3, k1*k2*k3, k0*k2*k3, k1^2*k3, k0*k1*k3, k0^2*k3,
			k2^3, k1*k2^2, k0*k2^2, k1^2*k2, k0*k1*k2, k0^2*k2, k1^3, k0*k1^2, k0^2*k1, k0^3];
		xi0 := &+[ai[j]*ki[j] : j in [1..#ki]];
		xi1 := &+[bi[j]*ki[j] : j in [1..#ki]];
		xi2 := &+[ci[j]*ki[j] : j in [1..#ki]];
		xi3 := &+[di[j]*ki[j] : j in [1..#ki]];
		Append(~codomain_other_points, Knew ! [xi0,xi1,xi2,xi3]);
	end for;
	
	return Jnew, codomain_points, codomain_other_points;
end function;


function BFT_chain(J, kernel, other_points)

	n := b-2;
	pos := 1;
	indices := [0];
	pos := 1;
	kernel_aux := [KummerSurface(J) ! P : P in kernel];
	other_points := [KummerSurface(J) ! P : P in other_points];
	indices := [0];
	for i := 0 to n-2 do
		gap := n-i-1 - indices[pos];
		if gap eq 0 then
		kernel2 := [Points(J, D)[1] : D in kernel_aux[2*pos-1..2*pos]];
		if not indices[pos] eq 0 then
				Prune(~indices);
				Prune(~kernel_aux);
				Prune(~kernel_aux);
				pos -:= 1;
			end if;
		elif gap eq 1 then
		kernel2 := [3*Points(J, D)[1] : D in kernel_aux[2*pos-1..2*pos]];
		if not indices[pos] eq 0 then
				Prune(~indices);
				Prune(~kernel_aux);
				Prune(~kernel_aux);
				pos -:= 1;
		end if;
		else
		new_ind := indices[pos] + Floor(gap/2);
		new_aux := kernel_aux[2*pos-1..2*pos];
		new_aux := [3^Floor(gap/2)*Points(J, P)[1] : P in new_aux];
		Append(~indices, new_ind);
		kernel_aux cat:=  [KummerSurface(J) ! D : D in new_aux];
		pos +:= 1;
		new_aux := [3^Ceiling(gap/2)*D : D in new_aux];
		kernel2 := new_aux;
		end if;
	
		J, kernel_aux, other_points := BFT_evaluation(kernel2, [KummerSurface(J) ! P : P in kernel_aux], other_points);
	end for;

	return J, kernel_aux, other_points;

end function;


/*
The final step in the attack are the splitting formulae, which are determined by the following functions.
*/

function get_ABCD_transform_split(f,kernel)
	/*
	Input: hyperelliptic polynomial of a split Jacobian
	Output: a,b,c,d,e parameters from the parametrization of Bröker, Howe, Lauter, Stevenhagen; and the corresponding transformation
	*/
    xiT,xiS := Explode(kernel);
    x0,x1,x2,x3 := Explode(xiT);
    y0,y1,y2,y3 := Explode(xiS);
	Knew<aux1,aux2,beta,gamma,delta,epsilon,a,b,c> := PolynomialRing(Fp2,9,"lex");
	Lnew<aux1,aux2,beta,gamma,delta,epsilon,a,b,c> := FieldOfFractions(Knew);
    Kx<x>:= PolynomialRing(Lnew);
	d := (1-12*a*c)/(16*b);
    alpha := 1;
	Delta1 := a^3+b^2;
	Delta2 := c^3+d^2;
	F1 := x^3 + 3*a*x + 2*b;
	F2 := 2*d*x^3 + 3*c*x^2 + 1;
	Fabcd := F1*F2;
	/* 
	Apply coordinate transformation x = (alpha*xprime + beta)/(gamma*x + delta) and y = epsilon*yprime/(gamma*x+delta)^3
	Inverse is xprime = (delta*x-beta)/(alpha-gamma*x) and yprime =(alpha*delta-beta*gamma)^3 y/((-gamma*x + alpha)^3*epsilon)
	*/
	newf := Kx ! (epsilon*Evaluate(f, (alpha*x+beta)/(gamma*x+delta))*(gamma*x+delta)^6);
	rel1 := [12*a*c + 16*b*d -1, aux1*Delta1-1, aux2*Delta2-1];
	rel2 := Coefficients(newf - Fabcd);
	/* Kernel condition*/
	xx0 := gamma^2*x2 - gamma*alpha*x1 + alpha^2*x0;
	xx1 := -2*delta*gamma*x2 + (beta*gamma + alpha*delta)*x1 - 2*beta*alpha*x0;
	xx2 := delta^2*x2 - delta*beta*x1 + beta^2*x0;
	yy0 := gamma^2*y2 - gamma*alpha*y1 + alpha^2*y0;
	yy1 := -2*delta*gamma*y2 + (beta*gamma + alpha*delta)*y1 - 2*beta*alpha*y0;
	yy2 := delta^2*y2 - delta*beta*y1 + beta^2*y0;
	rel3 := [xx0^2 + 4*c*(xx1^2-xx0*xx2) - 8*d*xx1*xx2, xx2^2 + 4*a*(xx1^2-xx0*xx2) - 8*b*xx0*xx1];
	rel4 := [yy0^2 + 4*c*(yy1^2-yy0*yy2) - 8*d*yy1*yy2, yy2^2 + 4*a*(yy1^2-yy0*yy2) - 8*b*yy0*yy1];
	relations := [Knew ! Numerator(el): el in rel1 cat rel2 cat rel3 cat rel4];
	/*
	Note: rel 3 and rel4 are not needed, but the GB computation is faster with the information
	*/
    I := ideal<Knew |  relations>;
	GB := GroebnerBasis(I);
	c := 1; // We guess if c is a square or not.
	rts := Roots(UnivariatePolynomial(Evaluate(GB[8],9,c)));
	if #rts eq 0 then
		c := NSQ;
		rts := Roots(UnivariatePolynomial(Evaluate(GB[8],9,c)));
		if #rts eq 0 then
		print "something is wrong with our assumption";
		end if;
	end if;
	b := rts[1][1];
	a := - Coefficients(Evaluate(Evaluate(GB[7], 9,c),8,b))[2];
	d := (1-12*a*c)/(16*b);
	epsilon := - Coefficients(Evaluate(Evaluate(GB[6], 9,c),8,b))[2];
	delta := - Coefficients(Evaluate(Evaluate(GB[5], 9,c),8,b))[2];
	gamma := - Coefficients(Evaluate(Evaluate(GB[4], 9,c),8,b))[2];
	beta := - Coefficients(Evaluate(Evaluate(GB[3], 9,c),8,b))[2];
	return a,b,c,d, [alpha,beta,gamma,delta,epsilon];
end function;


function get_split_curves(a,b,c,d)
	Delta1 := a^3+b^2;
	Delta2 := c^3+d^2;
	F1 := x^3 + 3*a*x + 2*b;
	F2 := 2*d*x^3 + 3*c*x^2 + 1;
	F := F1*F2;
	f1 := x^3 + 12*(2*a^2*d - b*c)*x^2 +12*(16*a*d^2 + 3*c^2)*Delta1*x + 512 * Delta1^2*d^3;
	f2 := x^3 + 12*(2*b*c^2 - a*d)*x^2 +12*(16*b^2*c + 3*a^2)*Delta2*x + 512 * Delta2^2*b^3;
	return F,f1,f2;
end function;


function apply_transformation(transform, points, f,newf)
	Kx<x> := PolynomialRing(Fp2);
	C := HyperellipticCurve(newf);
	J := Jacobian(C);
	newK := KummerSurface(J);
	a,b,c,d,e := Explode(transform);
	f0,f1,f2,f3,f4,f5,f6 := Explode(Coefficients(f));
	ac := a*c;
	bd := b*d;
	abcd := ac*bd;
	bcpad := b*c + a*d;

	l0 := (-2) * (ac)^2 * (3*(bcpad)^2 - 8*abcd)*f0 + (2) * ac * (bcpad) * ((bcpad)^2 - 2*abcd)*f1 + (-4) * abcd * ((bcpad)^2 - 2*abcd) * f2 + bd * (bcpad)^3 * f3 + (-2) * (bd)^2  * (bcpad)^2* f4 + (4) * (bd)^3 * (bcpad) *f5 + (-8) * (bd)^4 *f6 ;
	l2 := (-8) * (ac)^4 *f0 + (4) * (ac)^3 * (bcpad) *f1 + (-2) * (ac)^2 * (bcpad)^2 * f2 + ac * (bcpad)^3*f3 + (-4) * abcd * (b^2*c^2 + a^2*d^2) * f4 + (2) * bd * (bcpad) * (b^2*c^2 + a^2*d^2) * f5 + (-2) * (bd)^2 * (3*b^2*c^2 - 2*abcd + 3*a^2*d^2) * f6;
	l1 := (-4) * (ac)^3 * (bcpad)*f0 + (ac)^2 * ((bcpad)^2 + 4*abcd) * f1 + (-4) * abcd*a*c * (bcpad)*f2 + abcd * ((bcpad)^2 + 4*abcd)*f3 + (-4) * ac * (bd)^2 * (bcpad)*f4 + (bd)^2 * ((bcpad)^2 + 4*abcd)* f5 + (-4) * (bd)^3 * (bcpad)*f6;
	images := [];
	for xx in points do
		y1 := xx[3]*c^2 + xx[2]*c*d + xx[1]*d^2;
		y2 := 2*xx[3]*a*c + xx[2]*(bcpad) + 2*xx[1]*b*d;
		y3 := xx[3]*a^2 + xx[2]*a*b + xx[1]*b^2;
		y4 := e*((a*d-b*c)^4*xx[4] + l2*xx[3] + l1*xx[2] + l0*xx[1]);
		images := Append(images,newK![y1,y2,y3,y4]);
	end for;
	return images;
end function;


function get_splitting_maps(a,b,c,d)
	R<xi0,xi1,xi2,xi3> := PolynomialRing(Fp2,4);
	phi1x := (1/b)* ((6*a^3*c + 2/3*b^2*c - 1/2*a^2)*xi0^4 + (-40/3*a*b*c + 8/9*b)*xi0^3*xi1 + (48*a^3*c^2 + 48*b^2*c^2 - 10*a^2*c + 1/2*a)*xi0^2*xi1^2 + (96*a^3*c^3 + 96*b^2*c^3 - 2*a*c + 1/9)*xi1^4 + (-48*a^3*c^2 - 16*b^2*c^2 - 4*a^2*c + 2/3*a)*xi0^3*xi2 + ((72*a^4*c^2 + 120*a*b^2*c^2 - 12*a^3*c - 19/3*b^2*c + 1/2*a^2)/b)*xi0^2*xi1*xi2 + (-192*a^3*c^3 - 192*b^2*c^3 - 8*a^2*c^2 + 3*a*c - 1/12)*xi0*xi1^2*xi2 + ((288*a^4*c^3 + 288*a*b^2*c^3 - 36*a^3*c^2 - 12*b^2*c^2 + 1/12*a)/b)*xi1^3*xi2 + (96*a^3*c^3 + 96*b^2*c^3 + 64*a^2*c^2 - 9/2*a*c - 1/8)*xi0^2*xi2^2 + ((-288*a^4*c^3 - 288*a*b^2*c^3 + 48*a^3*c^2 + 8*b^2*c^2 - 2*a^2*c)/b)*xi0*xi1*xi2^2 + ((216*a^5*c^3 + 216*a^2*b^2*c^3 - 54*a^4*c^2 - 22*a*b^2*c^2 + 9/2*a^3*c + 1/3*b^2*c - 1/8*a^2)/b^2)*xi1^2*xi2^2 + (-96*a^2*c^3 - 12*a*c^2 + 5/3*c)*xi0*xi2^3 + ((-48*a^3*c^3 + 48*b^2*c^3 + 28*a^2*c^2 - 11/3*a*c + 5/36)/b)*xi1*xi2^3 + ((-72*a^4*c^3 + 24*a*b^2*c^3 + 18*a^3*c^2 - 2*b^2*c^2 - 3/2*a^2*c + 1/24*a)/b^2)*xi2^4 + 1/9*b*xi0^3*xi3 + 4/3*b*c*xi0*xi1^2*xi3 + (4/3*a*c - 1/9)*xi1^3*xi3 + (-8/3*b*c)*xi0^2*xi2*xi3 + (-4*a*c + 1/3)*xi0*xi1*xi2*xi3 + 16*b*c^2*xi0*xi2^2*xi3 + (16*a*c^2 - 4/3*c)*xi1*xi2^2*xi3 + ((16*a^2*c^2 - 8/3*a*c + 1/9)/b)*xi2^3*xi3);
	phi1z := (xi0^2 + 4*c*(xi1^2 -xi0*xi2) -8*d*xi1*xi2)^2;
	phi2x :=  - 32/b* ((a^2*b^2 - 16/3*b^4*c)*xi0^4 + (-3/2*a^3*b + 8/3*a*b^3*c - 10/9*b^3)*xi0^3*xi1 + (-4*a^2*b^2*c - 5/6*a*b^2)*xi0^3*xi2 - 8/9*b^3*xi0^3*xi3 + (9*a^2*b^2*c - 1/6*a*b^2 + 16*b^4*c^2)*xi0^2*xi1^2 + (9*a^3*b*c - 1/4*a^2*b + 16*a*b^3*c^2)*xi0^2*xi1*xi2 + 2/3*a*b^2*xi0^2*xi1*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 3*a*b^2*c + 1/16*b^2)*xi0^2*xi2^2 - 1/2*a^2*b*xi0^2*xi2*xi3 + (-9*a^3*b*c + 3/8*a^2*b - 16*a*b^3*c^2 - 2/3*b^3*c)*xi0*xi1^3 + (-9/2*a^4*c + 3/8*a^3 - 8*a^2*b^2*c^2 - a*b^2*c + 1/24*b^2)*xi0*xi1^2*xi2 + (-15/4*a^2*b*c + 19/96*a*b - 4*b^3*c^2)*xi0*xi1*xi2^2 - 1/6*b^2*xi0*xi1*xi2*xi3 + (-3/8*a^3*c + 1/32*a^2 - 2*a*b^2*c^2 - 1/3*b^2*c)*xi0*xi2^3 + 1/12*a*b*xi0*xi2^2*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 1/3*a*b^2*c - 1/18*b^2)*xi1^4 + 1/18*b^2*xi1^3*xi3 + (9/8*a^3*c - 3/32*a^2 + 2*a*b^2*c^2 - 1/4*b^2*c)*xi1^2*xi2^2 - 1/24*a*b*xi1^2*xi2*xi3 + (5/12*a*b*c - 1/36*b)*xi1*xi2^3 + (1/64*a^2*c - 1/768*a + 1/4*b^2*c^2)*xi2^4 - 1/288*b*xi2^3*xi3);
	phi2z:=  (xi2^2  + 4*a*(xi1^2 -xi0*xi2)- 8*b*xi0*xi1)^2; 
	return phi1x,phi1z,phi2x,phi2z;
end function;


function split_evaluation(kernel, points)
	/*
	Input: a (3,3)-subgroup kernel of a Kummer surface, and additional points on the Kummer surface to evaluate the isogeny at
	Output: a product of elliptic curves, as well as the images of the auxiliary points under the isogeny
	*/
	J := Parent(kernel[1]);
	C := Curve(J);
	f := HyperellipticPolynomials(C);
	// Note: this is not the correct kernel on the Kummer, but all we need.
	coef1 := Coefficients(kernel[1][1]);
	kernel1 := [1, -coef1[2], coef1[1],0];
	coef2 := Coefficients(kernel[2][1]);
	kernel2 := [1, -coef2[2], coef2[1],0];
	A,B,C,D, transform := get_ABCD_transform_split(f, [kernel1,kernel2]);
	a,b,c,d,e := Explode(transform);
	F,f1,f2 := get_split_curves(A,B,C,D);
	transform_points := apply_transformation([d,-b,-c,a,e], points, f,F);
	if IsSquare(e) then
            T := 1; // This is the twist.
        else
            T := e;
            f1 := Evaluate(f1, x*T)/T^3;
            f2 := Evaluate(f2, x*T)/T^3;
        end if;
        E1 := EllipticCurve(f1);
	E2 := EllipticCurve(f2);
	phi1x,phi1z,phi2x,phi2z := get_splitting_maps(A,B,C,D);
	codomain_points := [];
	for point in transform_points do
		pt := Eltseq(point);
		u1 := Evaluate(phi1x,pt);
		v1 := T*Evaluate(phi1z,pt);
		u2 := Evaluate(phi2x,pt);
		v2 := T*Evaluate(phi2z,pt);
		Append(~codomain_points, [[u1,v1], [u2,v2]]);
	end for;
	return [E1,E2], codomain_points;
end function;


/*
The attack now relies on starting on (E_start_new x EA), quotienting out the (3^b,3^b)-subgroup < (10*2^a*PB_new, -phiPB), (10*2^a*QB_new, -phiQB) >
whilst pushing through the points (infty, PA_cod) and (infty, QA_cod) for certain <PA_cod, QA_cod> = EA[2^A] (that we will generate).
The codomain of this isogeny will then be (E_start x X) and the images of the pushed through points will be (Dual_phiA(PA_cod), ___) and (Dual_phiA(QA_cod), ___),
where we are not interested in the projection on X.
The kernel of Alice's secret isogeny is then given by <Dual_phiA(PA_cod)> or <Dual_phiA(QA_cod)>, whichever has order 2^a.
*/

/*
Function to extend Alice's isogeny by an arbitrary isogeny of degree 10.
*/

function extend_phi(EA, phiPB, phiQB)
	_, tor2 := HasRoot(DivisionPolynomial(EA,2));
	EA_ext2, phi2 := IsogenyFromKernel(EA, x-tor2);
	phi2_PB := phi2(phiPB); phi2_QB := phi2(phiQB);
	/*
	The x-coordinates of divpol live in Fp2 but their y-coordinates not.
	The easiest way to find a kernel polynomial is by naively trying to match linear factors of the division polynomial.
	*/
	divpol5 := DivisionPolynomial(EA_ext2,5);
	facs := [f[1] : f in Factorisation(divpol5)];
	found := false; i := 2;
	while not found do
		kernel_pol := facs[1]*facs[i];
		try EA_ext10, phi5 := IsogenyFromKernel(EA_ext2, kernel_pol); found := true; catch e; end try;
		i +:= 1;
	end while;
	phi10_PB := phi5(phi2_PB);
	phi10_QB := phi5(phi2_QB);
	return EA_ext10, phi10_PB, phi10_QB;
end function;

/*
Computing (10*2^a*PB, -phi_extPB), (10*2^a*QB, -phi_extQB) and renaming it (R1,S1) and (R2,S2);
*/

function get_Ri_Si(PB, phi_extPB, QB, phi_extQB);
	R1 := 10*2^a*PB;
	S1 := -phi_extPB;
	R2 := 10*2^a*QB;
	S2 := -phi_extQB;
	return R1, S1, R2, S2;
end function;


/*
Function to generate a 2^a-torsion basis for EA.
*/

function get_2a_torsion_EA_ext(EA)
	repeat
		PA_cod := 3^b*Random(EA);
		QA_cod := 3^b*Random(EA);
	until WeilPairing(PA_cod, QA_cod, 2^a)^(2^(a-1)) ne 1;
	return PA_cod, QA_cod;
end function;


function attack_Alice(E_start, PB, QB, EA, phiPB, phiQB)
	EA_ext, phi_extPB, phi_extQB := extend_phi(EA, phiPB, phiQB);
	// We only need a (3^(b-1),3^(b-1))-isogeny so multiplying by 3
	PB *:= 3; QB *:= 3; phi_extPB *:= 3; phi_extQB *:= 3;
	R1, S1, R2, S2 := get_Ri_Si(PB, phi_extPB, QB, phi_extQB);
	PA_cod, QA_cod := get_2a_torsion_EA_ext(EA_ext);

	// Gluing
	firstkernel := [[3^(b-2)*R1,3^(b-2)*S1],[3^(b-2)*R2,3^(b-2)*S2]];
	points := [[R1,S1],[R2,S2],[E_start ! 0, PA_cod],[E_start ! 0, QA_cod]];
	J, image_points := glue_evaluation(firstkernel, points, [E_start, EA_ext]);
	
	// (3,3)-isogenies between Jacobians
	kernel := image_points[1..2];
	other_points := image_points[3..4];
	J, kernel_aux, other_points := BFT_chain(J, kernel, other_points);
	
	// Splitting
	kernel_aux := [Points(J, kernel_pt)[1] : kernel_pt in kernel_aux];
	Ei, codomain_points := split_evaluation(kernel_aux, other_points);
	E1, E2 := Explode(Ei);
	if jInvariant(E1) eq jInvariant(E_start) then
		E := E1; f := HyperellipticPolynomials(E);
		x1 := codomain_points[1][1][1]; z1 := codomain_points[1][1][2]; y1 := SquareRoot(Evaluate(f,x1/z1));
		P1 := E ! [x1/z1,y1];
		x2 := codomain_points[2][1][1]; z2 := codomain_points[2][1][2]; y2 := SquareRoot(Evaluate(f,x2/z2));
		P2 := E ! [x2/z2,y2];
		_, iso := IsIsomorphic(E,E_start);
		P1 := iso(P1);
		P2 := iso(P2);
	elif jInvariant(E2) eq jInvariant(E_start) then E := E2;
		E := E2; f := HyperellipticPolynomials(E);
		x1 := codomain_points[1][2][1]; z1 := codomain_points[1][2][2]; y1 := SquareRoot(Evaluate(f,x1/z1));
		P1 := E ! [x1/z1,y1];
		x2 := codomain_points[2][2][1]; z2 := codomain_points[2][2][2]; y2 := SquareRoot(Evaluate(f,x2/z2));
		P2 := E ! [x2/z2,y2];
		_, iso := IsIsomorphic(E,E_start);
		P1 := iso(P1);
		P2 := iso(P2);
	else "Something wrong."; end if;
	if 2^(a-1)*P1 ne E_start ! 0 then P := P1;
	elif 2^(a-1)*P2 ne E_start ! 0 then P := P2;
	elif 2^(a-2)*P1 ne E_start ! 0 then P := P1; // Can happen if we took part of dual in extending Alice's isogeny
	elif 2^(a-2)*P2 ne E_start ! 0 then P := P2;
	else "very strange order..."; P := P1;
	end if;

	return P;

end function;


function verify_attack(P,EA)
	E_ := E_start;
	Prem := P;
	order := 2^a;
	while order ne 1 do
		local_kernel := (order div 2)*Prem;
		if local_kernel ne E_ ! 0 then
			E_, phiA := IsogenyFromKernel(E_, x-local_kernel[1]);
			Prem := phiA(Prem);
		end if;
		order div:= 2;
	end while;
	j1 := jInvariant(EA); j2 := jInvariant(E_);
	/*
	If we extend by a 2-isogeny which is part of the dual, we are
	"unlucky" but can still verify easily with the modular polynomial.
	*/
	class2 := ClassicalModularPolynomial(2);
	isomorph := j1 eq j2;
	two_isog := Evaluate(class2,[j1,j2]) eq 0;
	return isomorph or two_isog;
end function;



for i := 1 to 20 do
k_A_private, EA, phiPB, phiQB := Alices_computation(E_start, PA_pub, QA_pub, PB_pub, QB_pub);
time P := attack_Alice(E_start, PB, QB, EA, phiPB, phiQB);
assert verify_attack(P,EA);
end for;




