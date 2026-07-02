TEST ///
H = hashTable{(set {},0),(set {1,2},1),(set {3,4},1),(set {1,2,3,4},2)}
L = cyclicFlats H
assert (isWellDefined L)
P = poset(keys H, isSubset)
assert isSplit P
-- test basesOfCyclicFlats
-- test tutteRing?
-- test tuttePolynomial?
///

TEST ///
H2 = hashTable{(set {},0),(set {1,2},1),(set {2,3},1),(set {1,2,3},2)}
L2 = cyclicFlats H2
assert (not isWellDefined L2) --do we also want to check which axioms are not respected?
P2 = poset(keys H2, isSubset)
assert isSplit P2
///