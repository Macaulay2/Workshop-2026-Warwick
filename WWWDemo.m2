restart
needsPackage "ToricVectorBundles"
-- Unlike previously, the package now
-- interfaces with NormalToricVarieties.
X = toricProjectiveSpace 3
netList {{"rays:"} | rays X, {"max cones:"} | max X}
-- We have some standard constructors. For instance,
-- the tangent bundle has a very straightforward
-- set of filtrations.
TX = tangentBundle X; details TX
-- It can be hard to parse this data. However,
-- we can print out what the filtrations look like!
-- Now you can see that at index 1, the corresponding
-- ray appears in the filtration.
displayFiltrations TX
-- We can make line bundles of divisors too, which
-- also have an easy-to-understand description.
D = toricDivisor({1,2,-1,0},X)
-- Note how the index tracks the coefficient of the
-- corresponding ray.
L = lineBundle D; displayFiltrations L
-- We could also have obtained this line bundle by twisting
triv = trivialBundle(X,1);
L1 = twist(triv, {1,2,-1,0} ); displayFiltrations L1
-- We can use the method areIsomorphic by simply typing
L==L1
-- In addition to constructors, we may also apply operations
-- to vector bundles, like taking direct sums, tensor products and duals
displayFiltrations (E = L ++ dual TX)
-- We also have (torus-equivariant) maps between toric
-- bundles (this was not in the old package).
idmap = map(E,E, id_(QQ^(rank E))); idmap.map

-- Let's check the Euler exact sequence maps:

sumoflbs = lineBundle X_0 ++ lineBundle X_1 ++ lineBundle X_2 ++ lineBundle X_3;
f = map(sumoflbs,triv,matrix(QQ,{{1},{1},{1},{1}})); f.map
isWellDefined f
isInjective f
g = map(TX,sumoflbs, transpose sub(matrix rays X,QQ)); g.map
isWellDefined g
isSurjective g
-- It's also possible to construct kernels and images...
-- but we're not finished implementing that. Soon, we
-- can check exactness at the middle, by checking
-- that the kernel of g equals the image of f!








