"""
 Verfication of the gluing formulae in "Efficient Computation of (3,3)-isogenies"
 
 Startegy: Here, we show that consecutively applying the gluing and splitting 
 coincides with multiplication by 3 on E1 x E2.
 Since, we already showed that the splitting is correct, this verfies the correctness
 of the gluing formulae.
"""

K.<a,b,c> = QQ[]
d = (1-12*a*c)/(16*b)
Delta1 = a^3+b^2
Delta2 = c^3+d^2
L.<x1,y1,x2,y2> = Frac(K)[]
Delta1 = a^3+b^2
Delta2 = c^3+d^2

R.<x> = L[]
F1 = x^3 + 3*a*x + 2*b
F2 = 2*d*x^3 + 3*c*x^2 + 1
F = F1*F2
f0,f1,f2,f3,f4,f5,f6 = F.coefficients(sparse=False)

f_E1 = x^3 + 12*(2*a^2*d - b*c)*x^2 +12*(16*a*d^2 + 3*c^2)*Delta1*x + 512 * Delta1^2*d^3
f_E2 = x^3 + 12*(2*b*c^2 - a*d)*x^2 +12*(16*b^2*c + 3*a^2)*Delta2*x + 512 * Delta2^2*b^3

#our splitting maps from Proposition 4
def eval_splitting(xiP):
	[xi0,xi1,xi2,xi3] = xiP
	phi1x = (1/b)* ((6*a^3*c + 2/3*b^2*c - 1/2*a^2)*xi0^4 + (-40/3*a*b*c + 8/9*b)*xi0^3*xi1 + (48*a^3*c^2 + 48*b^2*c^2 - 10*a^2*c + 1/2*a)*xi0^2*xi1^2 + (96*a^3*c^3 + 96*b^2*c^3 - 2*a*c + 1/9)*xi1^4 + (-48*a^3*c^2 - 16*b^2*c^2 - 4*a^2*c + 2/3*a)*xi0^3*xi2 + ((72*a^4*c^2 + 120*a*b^2*c^2 - 12*a^3*c - 19/3*b^2*c + 1/2*a^2)/b)*xi0^2*xi1*xi2 + (-192*a^3*c^3 - 192*b^2*c^3 - 8*a^2*c^2 + 3*a*c - 1/12)*xi0*xi1^2*xi2 + ((288*a^4*c^3 + 288*a*b^2*c^3 - 36*a^3*c^2 - 12*b^2*c^2 + 1/12*a)/b)*xi1^3*xi2 + (96*a^3*c^3 + 96*b^2*c^3 + 64*a^2*c^2 - 9/2*a*c - 1/8)*xi0^2*xi2^2 + ((-288*a^4*c^3 - 288*a*b^2*c^3 + 48*a^3*c^2 + 8*b^2*c^2 - 2*a^2*c)/b)*xi0*xi1*xi2^2 + ((216*a^5*c^3 + 216*a^2*b^2*c^3 - 54*a^4*c^2 - 22*a*b^2*c^2 + 9/2*a^3*c + 1/3*b^2*c - 1/8*a^2)/b^2)*xi1^2*xi2^2 + (-96*a^2*c^3 - 12*a*c^2 + 5/3*c)*xi0*xi2^3 + ((-48*a^3*c^3 + 48*b^2*c^3 + 28*a^2*c^2 - 11/3*a*c + 5/36)/b)*xi1*xi2^3 + ((-72*a^4*c^3 + 24*a*b^2*c^3 + 18*a^3*c^2 - 2*b^2*c^2 - 3/2*a^2*c + 1/24*a)/b^2)*xi2^4 + 1/9*b*xi0^3*xi3 + 4/3*b*c*xi0*xi1^2*xi3 + (4/3*a*c - 1/9)*xi1^3*xi3 + (-8/3*b*c)*xi0^2*xi2*xi3 + (-4*a*c + 1/3)*xi0*xi1*xi2*xi3 + 16*b*c^2*xi0*xi2^2*xi3 + (16*a*c^2 - 4/3*c)*xi1*xi2^2*xi3 + ((16*a^2*c^2 - 8/3*a*c + 1/9)/b)*xi2^3*xi3);
	phi1z = (xi0^2 + 4*c*(xi1^2 -xi0*xi2) -8*d*xi1*xi2)^2;
	phi2x = - 32/b* ((a^2*b^2 - 16/3*b^4*c)*xi0^4 + (-3/2*a^3*b + 8/3*a*b^3*c - 10/9*b^3)*xi0^3*xi1 + (-4*a^2*b^2*c - 5/6*a*b^2)*xi0^3*xi2 - 8/9*b^3*xi0^3*xi3 + (9*a^2*b^2*c - 1/6*a*b^2 + 16*b^4*c^2)*xi0^2*xi1^2 + (9*a^3*b*c - 1/4*a^2*b + 16*a*b^3*c^2)*xi0^2*xi1*xi2 + 2/3*a*b^2*xi0^2*xi1*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 3*a*b^2*c + 1/16*b^2)*xi0^2*xi2^2 - 1/2*a^2*b*xi0^2*xi2*xi3 + (-9*a^3*b*c + 3/8*a^2*b - 16*a*b^3*c^2 - 2/3*b^3*c)*xi0*xi1^3 + (-9/2*a^4*c + 3/8*a^3 - 8*a^2*b^2*c^2 - a*b^2*c + 1/24*b^2)*xi0*xi1^2*xi2 + (-15/4*a^2*b*c + 19/96*a*b - 4*b^3*c^2)*xi0*xi1*xi2^2 - 1/6*b^2*xi0*xi1*xi2*xi3 + (-3/8*a^3*c + 1/32*a^2 - 2*a*b^2*c^2 - 1/3*b^2*c)*xi0*xi2^3 + 1/12*a*b*xi0*xi2^2*xi3 + (9/4*a^4*c - 3/16*a^3 + 4*a^2*b^2*c^2 + 1/3*a*b^2*c - 1/18*b^2)*xi1^4 + 1/18*b^2*xi1^3*xi3 + (9/8*a^3*c - 3/32*a^2 + 2*a*b^2*c^2 - 1/4*b^2*c)*xi1^2*xi2^2 - 1/24*a*b*xi1^2*xi2*xi3 + (5/12*a*b*c - 1/36*b)*xi1*xi2^3 + (1/64*a^2*c - 1/768*a + 1/4*b^2*c^2)*xi2^4 - 1/288*b*xi2^3*xi3);
	phi2z = (xi2^2  + 4*a*(xi1^2 -xi0*xi2)- 8*b*xi0*xi1)^2;
	return [[phi1x,phi1z], [phi2x,phi2z]]

#multiplication by 3 on the Kummer line of an elliptic curve y^2 = x^3 + a2*x^2 + a4*x + a6
def times3(coef,P):
	[a2,a4,a6] = coef
	[xP,zP] = P
	if zP == 0:
		return [1,0]
	else:
		x1 = xP/zP
		xR = (x1^9 + (-12*a4)*x1^7 + (-8*a2*a4 - 96*a6)*x1^6 + (30*a4^2 - 216*a2*a6)*x1^5 + (48*a2*a4^2 - 192*a2^2*a6 - 24*a4*a6)*x1^4 + (16*a2^2*a4^2 - 64*a2^3*a6 + 36*a4^3 - 112*a2*a4*a6 + 48*a6^2)*x1^3 + (24*a2*a4^3 - 96*a2^2*a4*a6 + 48*a4^2*a6)*x1^2 + (9*a4^4 - 24*a2*a4^2*a6 - 48*a2^2*a6^2 + 96*a4*a6^2)*x1 + 8*a4^3*a6 - 32*a2*a4*a6^2 + 64*a6^3)
		zR = (3*x1^4 + 4*a2*x1^3 + 6*a4*x1^2 + 12*a6*x1 - a4^2 + 4*a2*a6)^2
		return [xR,zR]

def JacToKummer(Div,F):
	#only implemented for the generic case
	f0,f1,f2,f3,f4,f5,f6 = F.coefficients(sparse=False)
	[A,B] = Div
	[a0,a1,a2] = A.coefficients()
	[b0,b1] = B.coefficients()
	xi0 = 1
	xi1 = -a1
	xi2 = a0
	phi = 2*f0*xi0^3 + f1*xi0^2*xi1 + 2*f2*xi0^2*xi2 + f3*xi0*xi1*xi2 + 2*f4*xi0*xi2^2 + f5*xi1*xi2^2 + 2*f6*xi2^3
	y1y2 = b1^2*xi2 + b0*b1*xi1 + b0^2*xi0
	xi3 = (phi-2*y1y2)/(xi1^2-4*xi0*xi2)
	return [xi0,xi1,xi2,xi3]

#formulae from Proposition 5 (to be verified here)
def eval_pullback_E1(P):
	[x1,y1] = P
	denA = (2*x1 - (12*c*b-16*d*a^2))^2 + a;
	A1 = -4*(a*x1+8*d*Delta1);
	A0 =  -8*(b*x1-6*c*Delta1);
	B1 =  -2*y1*( (2*x1 + 4*(4*a^2*d - 3*b*c))^3 +  2*(3*a*x1 + 6*a*(4*a^2*d  - 3*b*c) + b));
	B0 = -4*y1/a*(4*(a*x1 +  8*d*Delta1)^2 - Delta1);
	return [x^2 + A1/denA *x + A0/denA, B1/denA^2*x + B0/denA^2]

def eval_pullback_E2(Q):
	[x2,y2] = Q
	denC =  -8*(d*x2 - 2*(Delta2)*3*a);
	C1 =  -4*(c*x2  + 8*b*Delta2);
	C0 = (2*x2 + (16*b*c^2 - 12*a*d))^2 + c;
	D1 =  16*y2*(Delta2); 
	D0 =  -32*y2 * (4*Delta2*(3*a*(x2 + 4*b*c^2 -3*a*d) + b*c) - d*x2^2);
	return [x^2 + C1/denC *x +  C0/denC, D1/denC^2*x + D0/denC^2]

	
##############################################
####### Multiplication by 3 ##################
##############################################

### Elliptic Curve E1
[a6,a4,a2,a0] = f_E1.coefficients()
assert f_E1 == x^3 + a2*x^2+a4*x+a6
#P = [x1,y1], R =3*P
R1 = times3([a2,a4,a6],[x1,1])

### Elliptic Curve E2
[b6,b4,b2,b0] = f_E2.coefficients()
assert f_E2 == x^3 + b2*x^2+b4*x+b6
#Q = [x2,y2], S =3*Q
S1 = times3([b2,b4,b6],[x2,1])

##############################################
####### Gluing and Splitting #################
##############################################

#Restriction to E1:
#apply gluing
Div1 = eval_pullback_E1([x1,y1])
#apply splitting
xiP = JacToKummer(Div1, F)
[R2,aux1] = eval_splitting(xiP)



#Restriction to E2:
#apply gluing
Div2 = eval_pullback_E2([x2,y2])
#apply splitting
xiQ = JacToKummer(C1/denC, C0/denC, D1/denC^2, D0/denC^2, F)
[aux2,S2] = eval_splitting(xiQ)


##############################################
####### Verification #########################
##############################################

I = L.ideal([y1^2-f_E1(x1), y2^2-f_E2(x2)])

print("Restriction to E1 is correct")
print("check 1: ", aux1[1] == 0) #check that the image on E2 is trivial.
print("check 2: ",(numerator(R1[1]*R2[0] - R2[1]*R1[0])).reduce(I) == 0) # check that the image on E1 is multiplication by 3.
print("Restriction to E2 is correct")
print("check 1: ", aux2[1] == 0) #check that the image on E1 is trivial.
print("check 2: ",(numerator(S1[1]*S2[0] - S2[1]*S1[0])).reduce(I) == 0) # check that the image on E1 is multiplication by 3.
