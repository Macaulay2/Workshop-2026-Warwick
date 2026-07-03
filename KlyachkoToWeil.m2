needsPackage "NormalToricVarieties";
needsPackage "ToricVectorBundles";

weilDecoration := (V) -> (
	L:=flatten (filtrationJumps V);
	amin:=min(L);
	amax:=max(L);
	d:=length (filtrationJumps V);
	alist:= reverse(toList(toList (d:amin).. toList (d:amax)));
	strataIntersections:={};
	weilDecorationImage:={};
	for a in alist do (	strata:={}; 
		for i from 0 to d-1 do(
			strata = append (strata,filteredPiece (V, (rays (variety V))#i, a#i));
		);
		int:=intersect (apply (strata, i -> image i));
		if isMember(int,strataIntersections)==false then (strataIntersections= append (strataIntersections, int);
			weilDecorationImage= append (weilDecorationImage, a));
	);
	wDecoration:={{strataIntersections#0,infinity}};
	for i from 1 to length (weilDecorationImage)-1 do (
		wDecoration= append (wDecoration, {gens strataIntersections#i,weilDecorationImage#i});
	);
	{variety V, wDecoration}
)

weilToKlyachko (NormalToricVariety, list, list) := (X,E,D) ->(
	L:=flatten D;
	amin:= min L;
	amax:= max L;

	H=new MutableHashTable;
	
	(M,J)= to sequence transpose for i from 0 to #(rays X)-1 do (

	);


)


--Test 
--Checking weilDecoration on the direct sum of the tangent bundle with a line bundle on P2.
TEST ///
M=toricProjectiveSpace 2;
V=tangentBundle M++lineBundle(M_1);
W=weilDecoration V;
L={{0,infinity},{1,{1,0,0}},{2,{0,1,0}},{1,{0,0,1}},{3,{0,0,0}}};
WL= apply (W, i -> {rank i#0, i#1});
assert (L==WL);
///