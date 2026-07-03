needsPackage "CyclicFlats"
needsPackage "Matroids"

H1 = new HashTable from {{} =>0,  {1,2,3,4} => 2}
M1 = cyclicFlatsMatroid(H1)
tuttePolynomial M1
tuttePolynomial uniformMatroid(2,4)

H2 = merge(H1, new HashTable from {{3,4} => 1}, last)
M2 = cyclicFlatsMatroid(H2)
tuttePolynomial M2
tuttePolynomial matroid(basesOfCyclicFlats(M2))

H4 = new HashTable from {{} =>0, {1,2,3} => 2, {2,3,4} => 2, {1,2,3,4,5,6} => 3}
M4 = cyclicFlatsMatroid(H4)

H5 = new HashTable from {{} =>0, toList(1..13) => 12,  toList(1..26) => 13}
M5 = cyclicFlatsMatroid(H5)
tuttePolynomial M5

M = uniformMatroid(10,5)

B := basesOfCyclicFlats M5


