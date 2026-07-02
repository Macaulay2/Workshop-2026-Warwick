needsPackage "CyclicFlats"
needsPackage "Matroids"

H1 = new HashTable from {{} =>0,  {1,2,3,4} => 2}
M1 = cyclicFlats(H1)
tutte(M1)
tuttePolynomial uniformMatroid(2,4)

H2 = merge(H1, new HashTable from {{3,4} => 1}, last)
M2 = cyclicFlats(H2)
tutte(M2)
tuttePolynomial matroid(basesOfCyclicFlats(M2))

H4 = new HashTable from {{} =>0, {1,2,3} => 2, {2,3,4} => 2, {1,2,3,4,5,6} => 3}
M4 = cyclicFlats(H4)

H5 = new HashTable from {{} =>0, toList(1..14) => 13,  toList(1..28) => 14}
M5 = cyclicFlats(H5)
tutte(M5)
tuttePolynomial matroid basesOfCyclicFlats M5


