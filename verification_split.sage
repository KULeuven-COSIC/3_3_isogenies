"""
 Verfication of the splitting formulas in "Efficient Computation of (3,3)-isogenies"
 
 Startegy: We take two points P=(x1,y1), Q=(x2,y2) on the genus-2 curve C: Y^2=F(X) as in Proposition 3
 and compute the image of the split-isogeny of the divisor class D = [P + Q - D_{infinity}] in two different ways:
 * using the maps psi_i: C -> E_i provided by BHLS'15, and combining the output;
 * computing the image of the divisor in on the Kummer surface and using our new splitting maps (Proposition 4).
 In the end we verify that both computations yield the same output.
 To be more precise, we only compare the x-coordinates of the image points.
"""

K.<a,b,c> = QQ[]
d = (1-12*a*c)/(16*b)
Delta1 = a^3+b^2
Delta2 = c^3+d^2
L.<x1,y1,x2,y2> = Frac(K)[]
Delta1 = a^3+b^2
Delta2 = c^3+d^2

R.<x> = K[]
F1 = x^3 + 3*a*x + 2*b
F2 = 2*d*x^3 + 3*c*x^2 + 1
F = F1*F2

f_E1 = x^3 + 12*(2*a^2*d - b*c)*x^2 +12*(16*a*d^2 + 3*c^2)*Delta1*x + 512 * Delta1^2*d^3
f_E2 = x^3 + 12*(2*b*c^2 - a*d)*x^2 +12*(16*b^2*c + 3*a^2)*Delta2*x + 512 * Delta2^2*b^3

#maps from Proposition 3 (Proposition A.2 in BHLS)
r1 = 12*Delta1*(-2*d*x+c)/F1
s1 = Delta1*(16*d*x^3-12*c*x^2-1)/F1^2
r2 = 12*Delta2*x^2*(a*x-2*b)/F2
s2 = Delta2*(x^3+12*a*x-16*b)/F2^2

#addition on E1 and E2
def x_add_E1(P,Q):
	[xP,yP] = P
	[xQ,yQ] = Q
	lam = (yP-yQ)/(xP-xQ)
	return lam^2 - 12*(2*a^2*d - b*c) - (xP + xQ)

def x_add_E2(P,Q):
	[xP,yP] = P
	[xQ,yQ] = Q
	lam = (yP-yQ)/(xP-xQ)
	return lam^2 - 12*(2*b*c^2 - a*d) - (xP + xQ)

#formulae to be verified
def eval_splitting(xiP):
	[xi0,xi1,xi2,xi3] = xiP
	phi1x = (1/b)* ((6*a^3*c + 2/3*b^2*c - 1/2*a^2)*xi0^4 + (-40/3*a*b*c + 8/9*b)*xi0^3*xi1 + (48*a^3*c^2 + 48*b^2*c^2 - 10*a^2*c + 1/2*a)*xi0^2*xi1^2 + (96*a^3*c^3 + 96*b^2*c^3 - 2*a*c + 1/9)*xi1^4 + (-48*a^3*c^2 - 16*b^2*c^2 - 4*a^2*c + 2/3*a)*xi0^3*xi2 + ((72*a^4*c^2 + 120*a*b^2*c^2 - 12*a^3*c - 19/3*b^2*c + 1/2*a^2)/b)*xi0^2*xi1*xi2 + (-192*a^3*c^3 - 192*b^2*c^3 - 8*a^2*c^2 + 3*a*c - 1/12)*xi0*xi1^2*xi2 + ((288*a^4*c^3 + 288*a*b^2*c^3 - 36*a^3*c^2 - 12*b^2*c^2 + 1/12*a)/b)*xi1^3*xi2 + (96*a^3*c^3 + 96*b^2*c^3 + 64*a^2*c^2 - 9/2*a*c - 1/8)*xi0^2*xi2^2 + ((-288*a^4*c^3 - 288*a*b^2*c^3 + 48*a^3*c^2 + 8*b^2*c^2 - 2*a^2*c)/b)*xi0*xi1*xi2^2 + ((216*a^5*c^3 + 216*a^2*b^2*c^3 - 54*a^4*c^2 - 22*a*b^2*c^2 + 9/2*a^3*c + 1/3*b^2*c - 1/8*a^2)/b^2)*xi1^2*xi2^2 + (-96*a^2*c^3 - 12*a*c^2 + 5/3*c)*xi0*xi2^3 + ((-48*a^3*c^3 + 48*b^2*c^3 + 28*a^2*c^2 - 11/3*a*c + 5/36)/b)*xi1*xi2^3 + ((-72*a^4*c^3 + 24*a*b^2*c^3 + 18*a^3*c^2 - 2*b^2*c^2 - 3/2*a^2*c + 1/24*a)/b^2)*xi2^4 + 1/9*b*xi0^3*xi3 + 4/3*b*c*xi0*xi1^2*xi3 + (4/3*a*c - 1/9)*xi1^3*xi3 + (-8/3*b*c)*xi0^2*xi2*xi3 + (-4*a*c + 1/3)*xi0*xi1*xi2*xi3 + 16*b*c^2*xi0*xi2^2*xi3 + (16*a*c^2 - 4/3*c)*xi1*xi2^2*xi3 + ((16*a^2*c^2 - 8/3*a*c + 1/9)/b)*xi2^3*xi3);
	phi1z = (xi0^2 + 4*c*(xi1^2 -xi0*xi2) -8*d*xi1*xi2)^2;
	phi2x = - 32/b* ((a^2*b^2 - 16/3*b^4*c)*xi0^4 + (-3/2*a^3*b + 8/3*a*b^3*c - 10/9*b^3)*xi0^3*xi1 + (-4*a^2*b^2*c - 5/6*a*b^2)*xi0^3*xi2 - 8/9*b^3*xi0^3*xi3 + (9*a^2*b^2*c - 1/6*a*b^2 + 16*b^4*c^2)*xi0^2*xi1^2 + (9*a^3*b*c - 1/4*a^2*b + 16*a*b^3*c^2)*xi0^2*xi1*xi2 + 2/3*a*b^2*xi0^2*xi1*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 3*a*b^2*c + 1/16*b^2)*xi0^2*xi2^2 - 1/2*a^2*b*xi0^2*xi2*xi3 + (-9*a^3*b*c + 3/8*a^2*b - 16*a*b^3*c^2 - 2/3*b^3*c)*xi0*xi1^3 + (-9/2*a^4*c + 3/8*a^3 - 8*a^2*b^2*c^2 - a*b^2*c + 1/24*b^2)*xi0*xi1^2*xi2 + (-15/4*a^2*b*c + 19/96*a*b - 4*b^3*c^2)*xi0*xi1*xi2^2 - 1/6*b^2*xi0*xi1*xi2*xi3 + (-3/8*a^3*c + 1/32*a^2 - 2*a*b^2*c^2 - 1/3*b^2*c)*xi0*xi2^3 + 1/12*a*b*xi0*xi2^2*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 1/3*a*b^2*c - 1/18*b^2)*xi1^4 + 1/18*b^2*xi1^3*xi3 + (9/8*a^3*c - 3/32*a^2 + 2*a*b^2*c^2 - 1/4*b^2*c)*xi1^2*xi2^2 - 1/24*a*b*xi1^2*xi2*xi3 + (5/12*a*b*c - 1/36*b)*xi1*xi2^3 + (1/64*a^2*c - 1/768*a + 1/4*b^2*c^2)*xi2^4 - 1/288*b*xi2^3*xi3);
	phi2z = (xi2^2  + 4*a*(xi1^2 -xi0*xi2)- 8*b*xi0*xi1)^2;
	return [[phi1x,phi1z], [phi2x,phi2z]]


##############################################
####### Strategy 1 ###########################
##############################################

#compute the images of P and Q on E1 and E2.
imP_E1 = [r1(x1),s1(x1)*y1]
imQ_E1 = [r1(x2),s1(x2)*y2]
imP_E2 = [r2(x1),s2(x1)*y1]
imQ_E2 = [r2(x2),s2(x2)*y2]

#adding the output on E1
imR_E1 = x_add_E1(imP_E1, imQ_E1)
imR_E2 = x_add_E2(imP_E2, imQ_E2)


##############################################
####### Strategy 2 ###########################
##############################################

f0,f1,f2,f3,f4,f5,f6 = F.coefficients(sparse=False)

xi0 = 1
xi1 = x1+x2
xi2 = x1*x2
phi = 2*f0*xi0^3 + f1*xi0^2*xi1 + 2*f2*xi0^2*xi2 + f3*xi0*xi1*xi2 + 2*f4*xi0*xi2^2 + f5*xi1*xi2^2 + 2*f6*xi2^3
xi3 = (phi-2*y1*y2)/(x1-x2)^2

#our splitting maps from Proposition 4.
[im1, im2] = eval_splitting([xi0,xi1,xi2,xi3])

##############################################
####### Verification #########################
##############################################

I = L.ideal([y1^2-F(x1), y2^2-F(x2)])

term1 = numerator(imR_E1 - im1[0]/im1[1])
print("Image on E1 is correct: ", term1.reduce(I) == 0)
term2 = numerator(imR_E2 - im2[0]/im2[1])
print("Image on E2 is correct: ", term2.reduce(I) == 0)