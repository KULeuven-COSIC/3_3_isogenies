# (3-3)-isogenies
Magma and SageMath code to efficiently compute chains of (3,3)-isogenies

The files in this folder contain the Magma code associated to the following paper by Thomas Decru and Sabrina Kunzweiler:
(soon on eprint)

- The file 33_hash_BFT.m contains a CGL hash function based on (3,3)-isogenies between superspecial abelian surfaces.
Starting Jacobians are hardcoded together with a symplectic basis. As mentioned in the paper, the hash function is limited in input size.

- The file BFT_verification.m contains a symbolic verification that the optimized arithmetic for the BFT-parametrization is indeed correct.

- The file SIKEp751_attack.m contains an attack on the SIKEp751 parameters where we target Alice's key. By default, the program will run 20 times and time each attack.
The code can easily be adjusted to work for primes distinct from p = SIKEp751, but for an actual attack, certain other subtleties may arise (e.g. guessing some steps).

- The file symplectic_basis.m was used to generate the symplectic bases from the hash function in 33_hash_BFT.m

- The file uv_list.m are a short list of extra parameters to attack lower SIKE security levels.
Some rely on integer factorizations which are not trivial hence we added them here since we computed them anyway.

- The file verification_split.sage contains a script to verify that our splitting formulae are correct.

- The file verification_glue.sage contains a script to verify that our gluing formulae are correct. This is done by showing that they are the dual of our splitting formulae.
