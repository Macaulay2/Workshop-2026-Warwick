TEST ///
H = hashTable{(set {},0),(set {1,2},1),(set {3,4},1),(set {1,2,3,4},2)}
L = cyclicFlatsMatroid H
assert (isWellDefined L)
P = poset(keys H, isSubset)
assert isSplit P
assert (set basesOfCyclicFlats L3 == set{set{1,3},set{1,4},set{2,3},set{2,4}}) 
-- test tutteRing?
-- test tuttePolynomial?
///

TEST ///
H2 = hashTable{(set {},0),(set {1,2},1),(set {2,3},1),(set {1,2,3},2)}
L2 = cyclicFlatsMatroid H2
assert (not isWellDefined L2) --do we also want to check which axioms are not respected?
P2 = poset(keys H2, isSubset)
assert isSplit P2
///

TEST///
H3 = hashTable{(set{},0), (set{3,4},1), (set{1,2,3,4},2)}
L3 = cyclicFlatsMatroid H3
assert isWellDefined L3
P3 = poset(keys H3, isSubset)
assert isSplit P3
assert (set basesOfCyclicFlats L3 == set{set{1,2},set{1,3},set{1,4},set{2,3},set{2,4}}) 
///

TEST///
H4 = hashTable{(set{},0),(set{1,2,3,4,5},2)}
L4 = cyclicFlatsMatroid H4
assert isWellDefined L4
P4 = poset(keys H4, isSubset)
assert not isSplit P4
assert (set basesOfCyclicFlats L4 == set{set{1,2},set{1,3},set{1,4},set{1,5},set{2,3},set{2,4},set{2,5},set{3,4},set{3,5},set{4,5}}) 
///

TEST///
H5 = new HashTable from {{} =>0, {1,2,3} => 2, {4,5,6} => 2, {1,2,3,4,5,6} => 3}
M5 = cyclicFlatsMatroid(H5)
assert isWellDefined M5
P5 = poset(keys H5, isSubset)
assert isSplit H5
-- assert (tuttePolynomial M5 == tuttePolynomial matroid(basesOfCyclicFlats(M5))) is not working b/c problem in Matroids.m2 tuttePolynomial
///