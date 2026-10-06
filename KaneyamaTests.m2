-------------------------------------------
-- TESTS for the Kaneyama bundles
-------------------------------------------
-- Test n+1
TEST ///
T = toricVectorBundleKaneyama(2,pp1ProductFan 2)
assert(T#"baseChangeTable" === hashTable {(0,1) => map(QQ^2,QQ^2,1),(0,2) => map(QQ^2,QQ^2,1),(1,3) => map(QQ^2,QQ^2,1),(2,3) => map(QQ^2,QQ^2,1)})
assert(T#"degreeTable" === hashTable apply(facesAsCones(0,pp1ProductFan 2), C -> (rays C, linealitySpace C) => map(ZZ^2,ZZ^2,0)))
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
L1 = {matrix {{1,0},{0,1}},matrix{{0,1},{1,0}},matrix{{-1,0},{-1,1}}}
L2 = {matrix {{-1,0},{0,-1}},matrix{{0,1},{1,0}},matrix{{0,-1},{-1,0}}}
T = toricVectorBundleKaneyama(2,projectiveSpaceFan 2,L1,L2)
assert(T#"baseChangeTable" === hashTable {(0,1) => matrix {{-1/1,0},{0,-1}},(0,2) => matrix{{0/1,1},{1,0}},(1,2) => matrix{{0/1,-1},{-1,0}}})
assert(T#"degreeTable" === hashTable {(matrix {{1,-1},{0,-1}}, map(ZZ^2,0,0)) => matrix{{-1,0},{-1,1}}, (matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{0,1},{1,0}}, (matrix {{-1,0},{-1,1}}, map(ZZ^2,0,0)) => matrix{{1,0},{0,1}}})
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
///


-- Test n+2
-- Checking tangentBundle for Kaneyama
TEST ///
T = tangentBundleKaneyama(pp1ProductFan 2)
assert(T#"baseChangeTable" === hashTable {(0,1) => map(QQ^2,QQ^2,{{1, 0}, {0, -1}}), (0,2) => map(QQ^2,QQ^2,{{-1, 0}, {0, 1}}), (1,3) => map(QQ^2,QQ^2,{{-1, 0}, {0, 1}}), (2,3) => map(QQ^2,QQ^2,{{1, 0}, {0, -1}})})
assert(T#"degreeTable" === hashTable {(matrix {{-1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{1,0},{0,-1}},(matrix {{-1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{1,0},{0,1}},(matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{-1,0},{0,-1}}, (matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{-1,0},{0,1}}})
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
T = tangentBundleKaneyama(projectiveSpaceFan 3)
assert(T#"baseChangeTable" === hashTable {(0,1) => map(QQ^3,QQ^3,{{1, -1, 0}, {0, -1, 0}, {0, -1, 1}}), (0,2) => map(QQ^3,QQ^3,{{-1, 0, 0}, {-1, 1, 0}, {-1, 0, 1}}), (1,2) => map(QQ^3,QQ^3,{{-1, 1, 0}, {-1, 0, 0}, {-1, 0, 1}}), (0,3) => map(QQ^3,QQ^3,{{1, 0, -1}, {0, 0, -1}, {0, 1, -1}}), (1,3) => map(QQ^3,QQ^3,{{1, 0, -1}, {0, 1, -1}, {0, 0, -1}}), (2,3) => map(QQ^3,QQ^3,{{0, 0, -1}, {1, 0, -1}, {0, 1, -1}})})
assert(T#"degreeTable" === hashTable {(matrix {{1,0,0},{0,1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{-1,0,0},{0,-1,0},{0,0,-1}},(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0},{0,0,-1},{1,1,1}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{1,1,1},{0,-1,0},{0,0,-1}}, (matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0},{1,1,1},{0,0,-1}}})
assert(rank T == 3)
assert(T#"dimension of the variety" == 3)
///

-- Test n+3
-- Checking cotangentBundle for Kaneyama
TEST ///
T = cotangentBundleKaneyama(hirzebruchFan 3)
assert(T#"baseChangeTable" === hashTable {(0,1) => map(QQ^2,QQ^2,{{1, 0}, {0, -1}}), (0,2) => map(QQ^2,QQ^2,{{-1, 3}, {0, 1}}), (1,3) => map(QQ^2,QQ^2,{{-1, -3}, {0, 1}}), (2,3) => map(QQ^2,QQ^2,{{1, 0}, {0, -1}})})
assert(T#"degreeTable" === hashTable {(matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{1,0},{0,-1}},(matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{1,0},{0,1}},(matrix {{0,-1},{1,3}}, map(ZZ^2,0,0)) => matrix{{-1,3},{0,1}}, (matrix {{0,-1},{-1,3}}, map(ZZ^2,0,0)) => matrix{{-1,-3},{0,-1}}})
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
T = cotangentBundleKaneyama(pp1ProductFan 3)
assert(T#"baseChangeTable" === hashTable {(2,6) => matrix{{-1_QQ,0,0},{0,1,0},{0,0,1}}, (4,5) => matrix{{1_QQ,0,0},{0,1,0},{0,0,-1}}, (4,6) => matrix{{1_QQ,0,0},{0,-1,0},{0,0,1}}, (3,7) => matrix{{-1_QQ,0,0},{0,1,0},{0,0,1}}, (5,7) => matrix{{1_QQ,0,0},{0,-1,0},{0,0,1}}, (6,7) => matrix{{1_QQ,0,0},{0,1,0},{0,0,-1}}, (0,1) => matrix{{1_QQ,0,0},{0,1,0},{0,0,-1}}, (0,2) => matrix{{1_QQ,0,0},{0,-1,0},{0,0,1}}, (1,3) => matrix{{1_QQ,0,0},{0,-1,0},{0,0,1}}, (0,4) => matrix{{-1_QQ,0,0},{0,1,0},{0,0,1}}, (2,3) => matrix{{1_QQ,0,0},{0,1,0},{0,0,-1}}, (1,5) => matrix{{-1_QQ,0,0},{0,1,0},{0,0,1}}})
assert(T#"degreeTable" === hashTable {(matrix {{1,0,0},{0,1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{1,0,0},{0,1,0},{0,0,1}},(matrix {{-1,0,0},{0,1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{-1,0,0},{0,1,0},{0,0,1}},(matrix {{1,0,0},{0,-1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{1,0,0},{0,-1,0},{0,0,1}},(matrix {{1,0,0},{0,1,0},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{1,0,0},{0,1,0},{0,0,-1}},(matrix {{-1,0,0},{0,-1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{-1,0,0},{0,-1,0},{0,0,1}},(matrix {{-1,0,0},{0,1,0},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{-1,0,0},{0,1,0},{0,0,-1}},(matrix {{1,0,0},{0,-1,0},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{1,0,0},{0,-1,0},{0,0,-1}},(matrix {{-1,0,0},{0,-1,0},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{-1,0,0},{0,-1,0},{0,0,-1}}})
assert(rank T == 3)
assert(T#"dimension of the variety" == 3)
///

-- Test n+4
-- Checking deltaE for Kaneyama
TEST ///
T = toricVectorBundleKaneyama(3,projectiveSpaceFan 2)
assert(deltaEKaneyama T == convexHull matrix{{0},{0}})
T = tangentBundleKaneyama(projectiveSpaceFan 2)
assert(deltaEKaneyama T == convexHull matrix {{-1,2,-1},{-1,-1,2}})
T = cotangentBundleKaneyama(pp1ProductFan 3)
assert(deltaEKaneyama T == convexHull matrix {{-1,1,-1,1,-1,1,-1,1},{-1,-1,1,1,-1,-1,1,1},{-1,-1,-1,-1,1,1,1,1}})
///

-- Test n+5
-- Checking cohomology for Kaneyama
TEST ///
T = toricVectorBundleKaneyama(2,pp1ProductFan 2)
assert(sort degrees cohomology(0,T,matrix{{0},{0}}) == sort degrees (ring T)^{{0,0},{0,0}})
assert(sort degrees cohomology(0,T) == sort degrees (ring T)^{{0,0},{0,0}})
assert(sort degrees cohomology(1,T) == sort degrees (ring T)^0)
assert(sort degrees cohomology(2,T) == sort degrees (ring T)^0)
T1 = tangentBundleKaneyama(pp1ProductFan 2)
assert(sort degrees cohomology(0,T1,matrix{{0},{0}}) == sort degrees (ring T1)^{{0,0},{0,0}})
assert(sort degrees cohomology(0,T1,matrix{{1},{1}}) == sort degrees (ring T1)^0)
assert(sort degrees cohomology(0,T1) == sort degrees (ring T1)^{{1,0},{0,1},{0,0},{0,0},{0,-1},{-1,0}})
assert(sort degrees cohomology(1,T1) == sort degrees (ring T1)^0)
assert(sort degrees cohomology(2,T1) == sort degrees (ring T1)^0)
T = tangentBundleKaneyama(hirzebruchFan 3 * projectiveSpaceFan 1)
assert(cohomology(0,T,{matrix {{2},{1},{0}}, matrix{{3},{1},{0}}}) == {(ring T)^{{-2,-1,0}},(ring T)^{{-3,-1,0}}})
assert(cohomology(1,T,{matrix {{-2},{-1},{0}}, matrix{{-1},{-1},{0}}}) == {(ring T)^{{2, 1, 0}},(ring T)^{{1, 1, 0}}})
assert(cohomology(2,T,matrix{{0},{0},{0}}) == (ring T)^0)
assert(cohomology(3,T,matrix{{0},{0},{0}}) == (ring T)^0)
///


-- Test n+6
-- Checking lineBundleKaneyama
TEST ///
T = lineBundleKaneyama({1,4,3,2},projectiveSpaceFan 3)
assert(T#"baseChangeTable" === hashTable {(0,1) => map(QQ^1,QQ^1,1),(0,2) => map(QQ^1,QQ^1,1),(0,3) => map(QQ^1,QQ^1,1),(1,2) => map(QQ^1,QQ^1,1),(1,3) => map(QQ^1,QQ^1,1),(2,3) => map(QQ^1,QQ^1,1)})
assert(T#"degreeTable" === hashTable {(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{-2},{-3},{6}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{8},{-3},{-4}},(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{-2},{7},{-4}}, (map(ZZ^3,ZZ^3,1), map(ZZ^3,0,0)) => matrix{{-2},{-3},{-4}}})
assert(rank T == 1)
assert(T#"dimension of the variety" == 3)

///

-- Test n+7
-- Checking directSum for Kaneyama
TEST ///
T1 = tangentBundleKaneyama(projectiveSpaceFan 3)
T2 = lineBundleKaneyama({1,7,5,3},projectiveSpaceFan 3)
T = T1 ++ T2
assert(T#"baseChangeTable" === hashTable {(0,1) => matrix{{1_QQ,-1,0,0},{0,-1,0,0},{0,-1,1,0},{0,0,0,1}}, (0,2) => matrix{{-1_QQ,0,0,0},{-1,1,0,0},{-1,0,1,0},{0,0,0,1}}, (1,2) => matrix{{-1_QQ,1,0,0},{-1,0,0,0},{-1,0,1,0},{0,0,0,1}}, (0,3) => matrix{{1_QQ,0,-1,0},{0,0,-1,0},{0,1,-1,0},{0,0,0,1}}, (1,3) => matrix{{1_QQ,0,-1,0},{0,1,-1,0},{0,0,-1,0},{0,0,0,1}}, (2,3) => matrix{{0_QQ,0,-1,0},{1,0,-1,0},{0,1,-1,0},{0,0,0,1}}})
assert(T#"degreeTable" === hashTable {(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0,-3},{0,0,-1,-5},{1,1,1,9}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{1,1,1,13},{0,-1,0,-5},{0,0,-1,-7}},(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0,-3},{1,1,1,11},{0,0,-1,-7}}, (map(ZZ^3,ZZ^3,1),map(ZZ^3,0,0)) => matrix{{-1,0,0,-3},{0,-1,0,-5},{0,0,-1,-7}}})
assert(rank T == 4)
assert(T#"dimension of the variety" == 3)
assert(T == directSum {T1,T2})
T1 = cotangentBundleKaneyama(hirzebruchFan 3)
T2 = tangentBundleKaneyama(hirzebruchFan 3)
T = T1 ++ T2
assert(T#"baseChangeTable" === hashTable {(0,1) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,-1}}, (0,2) => matrix{{-1_QQ,3,0,0},{0,1,0,0},{0,0,-1,0},{0,0,3,1}}, (1,3) => matrix{{-1_QQ,-3,0,0},{0,1,0,0},{0,0,-1,0},{0,0,-3,1}}, (2,3) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,-1}}})
assert(T#"degreeTable" === hashTable {(matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{1,0,-1,0},{0,-1,0,1}}, (matrix {{0,-1},{1,3}}, map(ZZ^2,0,0)) => matrix{{-1,3,1,-3},{0,1,0,-1}}, (matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{1,0,-1,0},{0,1,0,-1}}, (matrix {{0,-1},{-1,3}}, map(ZZ^2,0,0)) => matrix {{-1,-3,1,3},{0,-1,0,1}}})
assert(rank T == 4)
assert(T#"dimension of the variety" == 2)
///

-- Test n+8
-- Checking dual for Kaneyama
TEST ///
T = dual lineBundleKaneyama({1,4,3,2},projectiveSpaceFan 3)
assert(T#"baseChangeTable" === hashTable{(0,1) => matrix{{1_QQ}},(0,2) => matrix{{1_QQ}}, (0,3) => matrix{{1_QQ}}, (1,2) => matrix{{1_QQ}},(1,3) => matrix{{1_QQ}},(2,3) => matrix{{1_QQ}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{2},{3},{-6}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{-8},{3},{4}},(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{2},{-7},{4}}, (map(ZZ^3,ZZ^3,1), map(ZZ^3,0,0)) => matrix{{2},{3},{4}}})
assert(rank T == 1)
assert(T#"dimension of the variety" == 3)
T1 = tangentBundleKaneyama(projectiveSpaceFan 3)
T = dual(T1 ++ T)
assert(T#"baseChangeTable" === hashTable{(0,2) => matrix{{-1_QQ,-1,-1,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}},(0,1) => matrix{{1_QQ,0,0,0},{-1,-1,-1,0},{0,0,1,0},{0,0,0,1}}, (0,3) => matrix{{1_QQ,0,0,0},{-1,-1,-1,0},{0,1,0,0},{0,0,0,1}}, (1,2) => matrix{{0_QQ,1,0,0},{-1,-1,-1,0},{0,0,1,0},{0,0,0,1}},(1,3) => matrix{{1_QQ,0,0,0},{0,1,0,0},{-1,-1,-1,0},{0,0,0,1}},(2,3) => matrix{{-1_QQ,-1,-1,0},{1,0,0,0},{0,1,0,0},{0,0,0,1}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{0,1,0,-2},{0,0,1,-3},{-1,-1,-1,6}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{-1,-1,-1,8},{0,1,0,-3},{0,0,1,-4}},(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{0,1,0,-2},{-1,-1,-1,7},{0,0,1,-4}}, (map(ZZ^3,ZZ^3,1), map(ZZ^3,0,0)) => matrix{{1,0,0,-2},{0,1,0,-3},{0,0,1,-4}}})
assert(rank T == 4)
assert(T#"dimension of the variety" == 3)
///

-- Test n+9
-- Checking tensor for Kaneyama
TEST ///
T1 = tangentBundleKaneyama(pp1ProductFan 2)
T2 = cotangentBundleKaneyama(pp1ProductFan 2)
T = T1 ** T2
assert(T#"baseChangeTable" === hashTable{(0,2) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,1}},(0,1) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,1}}, (1,3) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,1}}, (2,3) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,1}}})
assert(T#"degreeTable" === hashTable{(matrix {{-1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{0,-1,1,0},{0,-1,1,0}},(matrix {{-1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{0,-1,1,0},{0,1,-1,0}},(matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{0,1,-1,0},{0,1,-1,0}}, (map(ZZ^2,ZZ^2,1), map(ZZ^2,0,0)) => matrix{{0,1,-1,0},{0,-1,1,0}}})
assert(rank T == 4)
assert(T#"dimension of the variety" == 2)
T1 = tangentBundleKaneyama(hirzebruchFan 2)
T2 = lineBundleKaneyama({5,1,7,3},hirzebruchFan 2)
T2 = T2 ++ T2
T = T1 ** T2
assert(T#"baseChangeTable" === hashTable{(0,1) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,-1}},(0,2) => matrix{{-1_QQ,0,0,0},{2,1,0,0},{0,0,-1,0},{0,0,2,1}}, (1,3) => matrix{{-1_QQ,0,0,0},{-2,1,0,0},{0,0,-1,0},{0,0,-2,1}}, (2,3) => matrix{{1_QQ,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,-1}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{-4,-3,-4,-3},{-1,-2,-1,-2}},(matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{-4,-3,-4,-3},{5,6,5,6}},(matrix {{0,-1},{-1,2}}, map(ZZ^2,0,0)) => matrix{{18,19,18,19},{5,6,5,6}},(matrix {{0,-1},{1,2}}, map(ZZ^2,0,0)) => matrix{{6,3,6,3},{-1,-2,-1,-2}}})
assert(rank T == 4)
assert(T#"dimension of the variety" == 2)
///

-- Test n+10
-- Checking symmetricPower for Kaneyama
TEST ///
T = tangentBundleKaneyama(projectiveSpaceFan 3)
T = symmetricPower(2,T)
assert(T#"baseChangeTable" === hashTable{(0,1) => matrix{{1_QQ,-1,0,1,0,0},{0,-1,0,2,0,0},{0,-1,1,2,-1,0},{0,0,0,1,0,0},{0,0,0,2,-1,0},{0,0,0,1,-1,1}},(0,2) => matrix{{1_QQ,0,0,0,0,0},{2,-1,0,0,0,0},{2,0,-1,0,0,0},{1,-1,0,1,0,0},{2,-1,-1,0,1,0},{1,0,-1,0,0,1}}, (0,3) => matrix{{1_QQ,0,-1,0,0,1},{0,0,-1,0,0,2},{0,1,-1,0,-1,2},{0,0,0,0,0,1},{0,0,0,0,-1,2},{0,0,0,1,-1,1}}, (1,2) => matrix{{1_QQ,-1,0,1,0,0},{2,-1,0,0,0,0},{2,-1,-1,0,1,0},{1,0,0,0,0,0},{2,0,-1,0,0,0},{1,0,-1,0,0,1}}, (1,3) => matrix{{1_QQ,0,-1,0,0,1},{0,1,-1,0,-1,2},{0,0,-1,0,0,2},{0,0,0,1,-1,1},{0,0,0,0,-1,2},{0,0,0,0,0,1}},(2,3) => matrix{{0_QQ,0,0,0,0,1},{0,0,-1,0,0,2},{0,0,0,0,-1,2},{1,0,-1,0,0,1},{0,1,-1,0,-1,2},{0,0,0,1,-1,1}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0,-2,-1,0},{2,2,2,2,2,2},{0,0,-1,0,-1,-2}},(matrix {{1,0,0},{0,1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{-2,-1,-1,0,0,0},{0,-1,0,-2,-1,0},{0,0,-1,0,-1,-2}},(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{0,-1,0,-2,-1,0},{0,0,-1,0,-1,-2},{2,2,2,2,2,2}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{2,2,2,2,2,2},{0,-1,0,-2,-1,0},{0,0,-1,0,-1,-2}}})
assert(rank T == 6)
assert(T#"dimension of the variety" == 3)
///

-- Test n+11
-- Checking exteriorPower for Kaneyama -- did we get rid of this?
TEST ///
T = cotangentBundleKaneyama(hirzebruch 3)
T = exteriorPower(2,T)
assert(T#"baseChangeTable" === hashTable{(0,1) => matrix{{-1_QQ}}, (0,2) => matrix{{-1_QQ}}, (1,3) => matrix{{-1_QQ}}, (2,3) => matrix{{-1_QQ}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,0},{0,1}}, map(ZZ^2,0,0)) => matrix{{1},{1}},(matrix {{1,0},{0,-1}}, map(ZZ^2,0,0)) => matrix{{1},{-1}},(matrix {{0,-1},{1,3}}, map(ZZ^2,0,0)) => matrix {{2},{1}},(matrix {{0,-1},{-1,3}}, map(ZZ^2,0,0)) => matrix {{-4},{-1}}})
assert(rank T == 1)
assert(T#"dimension of the variety" == 2)
T = tangentBundleKaneyama(projectiveSpaceFan 3)
T = exteriorPower(2,T)
assert(T#"baseChangeTable" === hashTable{(0,1) => matrix{{-1_QQ,0,0},{-1,1,-1},{0,0,-1}}, (0,2) => matrix{{-1_QQ,0,0},{0,-1,0},{1,-1,1}}, (0,3) => matrix{{0_QQ,-1,0},{1,-1,1},{0,0,1}}, (1,2) => matrix{{1_QQ,0,0},{1,-1,1},{0,-1,0}}, (1,3) => matrix{{1_QQ,-1,1},{0,-1,0},{0,0,-1}}, (2,3) => matrix{{0_QQ,1,0},{0,0,1},{1,-1,1}}})
assert(T#"degreeTable" === hashTable{(matrix {{1,-1,0},{0,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{-1,0,-1},{2,2,2},{0,-1,-1}},(matrix {{1,0,0},{0,1,0},{0,0,1}}, map(ZZ^3,0,0)) => matrix{{-1,-1,0},{-1,0,-1},{0,-1,-1}},(matrix {{1,0,-1},{0,1,-1},{0,0,-1}}, map(ZZ^3,0,0)) => matrix{{-1,0,-1},{0,-1,-1},{2,2,2}},(matrix {{0,-1,0},{1,-1,0},{0,-1,1}}, map(ZZ^3,0,0)) => matrix{{2,2,2},{-1,0,-1},{0,-1,-1}}})
assert(rank T == 3)
assert(T#"dimension of the variety" == 3)
///

-- Test n+12
-- Checking eulerChi for Kaneyama
TEST ///
T = tangentBundleKaneyama(hirzebruchFan 3)
u = matrix {{0},{0}}
assert(eulerChiKaneyama(u,T) == 2)
assert(eulerChiKaneyama T == 6)
///

-- Test n+13
-- Checking cartierIndex
TEST ///
C=posHull matrix {{1,2},{2,1}}
C1=posHull matrix {{1,-1},{2,-1}}
C2=posHull matrix {{2,-1},{1,-1}}
F=fan{C,C1,C2}
assert(cartierIndex({1,1,1},F) == 3)
assert(cartierIndex({3,3,3},F) == 1)
///


-- ADDING NEW TESTS JUNE/JULY 2026
-- Test n+14
-- Checking isWellDefined (Kaneyama) (combining the tests for cocycleCheck and regCheck)--TODO: FIX THIS
TEST ///
T = toricVectorBundleKaneyama(2,pp1ProductFan 2)
assert isWellDefined T
--tests for cocycleCheck
T1 = addBaseChange(T,{matrix{{1,2},{0,1}},matrix{{1,0},{3,1}},matrix{{1,-2},{0,1}},matrix{{1,0},{-3,1}}})
assert isWellDefined T1
T1 = addBaseChange(T,{matrix{{1,2},{0,1}},matrix{{1,0},{3,1}},matrix{{1,-2},{0,1}},matrix{{1,0},{-2,1}}})
assert not isWellDefined T1 -- fails because of cocycleCheck
--tests for regCheck
T1 = addDegrees(T,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
assert not isWellDefined T1 -- fails because of regCheck
T1 = addDegrees(T,{matrix{{-1,0},{-3,-1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{1,2},{3,1}}})
assert isWellDefined T1
///
