/*
This file contains factorizations for the SIKE parameters relevant to attacking Alice's secret key.
The first set are the factorizations of certain forms (3^b - d*2^a) eq (u+2*v*i)*(u-2*v*i).
The second set are the prime factorizations of those same forms, which were used to create the first set.
We mostly give this second set for the sake of completion since not all of them are trivial to factor.
*/

clear;
Zi<i> := GaussianIntegers();

//NIST1
b := 137; a := 216;
u := 402674151105657912862781414766195;
v := 346913530770977850100167994471768;
assert 3^138 - 2^215 eq (u+2*v*i)*(u-2*v*i);

//NIST2
b := 159; a := 250;
u := 111468973766268621775559316750599946817;
v := 23372592726320865963581407703105631952;
assert 3^160 - 4*2^250 eq (u+2*v*i)*(u-2*v*i);

//NIST3
b := 192; a := 305;
u := 16904874744919607653156699970172579372450738819;
v := 3945973145292960369122332320488598401289195520;
assert 3^194 - 2^303 eq (u+2*v*i)*(u-2*v*i);

u := 5328638271525982078477157434993556101042992383;
v := 1415565985869512842585690231652310011397231480;
assert 3^192 - 2^301 eq (u+2*v*i)*(u-2*v*i);

//NIST5
b := 239; a := 372;
u := 84727936279133751413846965905657949516597707407463528877;
v := 252700408455552999199462036016877991153973776652061243550;
assert 3^238 - 10*2^372 eq (u+2*v*i)*(u-2*v*i);



//NIST1
b := 137; a := 216;
N := 3^(b+1) - 2^(a-1);
facs := [41,57601,100574519561,2709413946502543533619717725856048139171953089721];
assert &and [IsPrime(f) : f in facs];
assert &and [(f mod 4) eq 1 : f in facs];
assert N eq &*facs;

//NIST2
b := 159; a := 250;
N := 3^(b+1) - 4*2^a;
facs := [5, 89, 677, 9461466064126669, 32969589013507337, 7271332493281930861, 21381037495911704609];
assert &and [IsPrime(f) : f in facs];
assert &and [(f mod 4) eq 1 : f in facs];
assert N eq &*facs;

//NIST3
b := 192; a := 305;
N := 3^(b+2) - 2^(a-2);
facs := [17, 84526489, 4798550205435911833, 69475856477760954735579365249, 726549863510963402885338756233452041];
assert &and [IsPrime(f) : f in facs];
assert &and [(f mod 4) eq 1 : f in facs];
assert N eq &*facs;
N := 3^b - 2^(a-4);
facs := [403961165782355279835963763698529, 90131668967880420240888857169564362802447941131434369601441];
assert &and [IsPrime(f) : f in facs];
assert &and [(f mod 4) eq 1 : f in facs];
assert N eq &*facs;

//NIST5
b := 239; a := 372;
N := 3^(b-1) - 10*2^a;
facs := [811493, 5013523175966487971929832048324548860450582620717, 64547806009231195371755029737104491765999960800178981242809];
assert &and [IsPrime(f) : f in facs];
assert &and [(f mod 4) eq 1 : f in facs];
assert N eq &*facs;


/*
//To obtain the first set from the second, it suffices to plug in a sequences of prime factors which are 1 mod 4:
facs := [811493, 5013523175966487971929832048324548860450582620717, 64547806009231195371755029737104491765999960800178981242809];
prod := 1;
for ell in facs do
 z := Integers() ! SquareRoot(GF(ell) ! -1);
 prod *:= GCD(z + i, ell);
end for;
prod;
//The coefficients of product are then (u,2v), where 2v is the even one.
*/
