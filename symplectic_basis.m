/*
The following function creates a symplectic basis for a Jacobian with full rational 3^power3-torsion.
It is not meant to be optimized but can easily be adjusted to change it to some other m-torsion.
*/

SymplecticBasisPowerThree := function(J,power3,cofactor)
  /*
   Symplectic Basis for the m-torsion of J (not deterministic), where m is 3^power3
   Output: (P1,P2,Q1,Q2) with  e_m(P1,Q1) = e_m(P2,Q2) = zeta (primitive m-th root)
                               e_m(Pi,Qj) = 1 (for i neq j)
                               e_m(Pi,Pj) = e_m(Qi,Qj) = 1
  
   Assumptions: (m*cofactor)^2 = #J[FF_p],
   for example in the SIDH setting: m=2^ea, cofactor = 3^eb,
  */
  m := 3^power3;
  P:=[];
  Q:=[];
  repeat
      P[1] := cofactor * Random(J);
  until 3^(power3-1)*P[1] ne Id(J);

  repeat
  	P[3] := cofactor * Random(J); //P[2]
    zeta := WeilPairing(P[1],P[3],m);
    print "round 2";
  until Order(zeta) eq m;
  Q[1] := P[3];

  repeat
    P[2] := cofactor * Random(J);
    alpha := [[Log(zeta,WeilPairing(P[i],P[j],m)): j in [1,2,3]]: i in [1,2,3]];
    P[2]:= P[2] - alpha[1][2]*P[3] + alpha[3][2]*P[1];
    print "round 3";
  until 3^(power3-1) *P[2] ne Id(J);

  repeat
    P[4] := cofactor * Random(J);
    a34 := Log(zeta,WeilPairing(P[2],P[4],m));
    print "round 4";
  until GCD(m,a34) eq 1;

  t1,t2,t3 := XGCD(m,a34);
  P[4] := t3*P[4];

  for i in [1,2,3] do
    alpha[i][4] := Log(zeta,WeilPairing(P[i],P[4],m));
  end for;

  Q[2] := P[4] + alpha[3][4]*P[1] - alpha[1][4]*P[3];

  return [P[1],P[2],Q[1],Q[2]];
end function;
