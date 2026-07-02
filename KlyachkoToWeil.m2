needsPackage "NormalToricVarieties";
needsPackage "ToricVectorBundles";

-*
jumpsToSubspaces (list, list, hashTable) := (fJumps,fMatrices,a) -> (
--if length a != length fJumps then error "The length of the vector a must match the number of filtration jumps.";
I={};
for i from 0 to #fJumps-1 do (J={}; 
	for j from 0 to length fJumps#i -1 do ((

		if (fJumps#i)#j >= a#i then J=append (J, (entries(fMatrices#i)_j)));
	
		Jspan=image transpose(map(E,E,matrix J)););
	I=append(I,Jspan););
S=intersect(I);
return S;
)
*-

M

--Test 34
--Checking areIsomorphic
--first test, check trivial bundles of different ranks are not isomorphic
TEST ///
M=toricProjectiveSpace 2;
V=tangentBundle M++lineBundle(M_1);
W=weilDecoration V;
L={{0,infinity},{1,{1,0,0}},{2,{0,1,0}},{1,{0,0,1}},{3,{0,0,0}}};
WL= apply (W, i -> {rank i#0, i#1});
assert (L==WL);
///