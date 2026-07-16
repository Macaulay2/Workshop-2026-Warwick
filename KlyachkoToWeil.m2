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
	--wDecoration:={{gens strataIntersections#0,infinity}};
        wDecoration := {};
	for i from 1 to length (weilDecorationImage)-1 do (
		wDecoration= append (wDecoration, {gens strataIntersections#i,weilDecorationImage#i});
	);
	wDecoration
)
-*
weilToKlyachko (NormalToricVariety, list, list) := (X,E,D) ->(
	L:=flatten D;
	amin:= min L;
	amax:= max L;

	H=new MutableHashTable;

	(M,J)= to sequence transpose for i from 0 to #(rays X)-1 do (

	);


)
*-

tvbPosetChains := (D,n) -> (
    if n < 0 then return error("need nonnegative n");
    if n == 0 then return apply(D,l -> {{numcols l_0, l_1}});
    divs := flatten tvbPosetChains(D,0);
    prevChains := tvbPosetChains(D,n-1);
    flatten for c in prevChains list (
        currdiv := first c;
        for newdiv in divs list (
            if currdiv_0 >= newdiv_0 then continue
            else
            if any(transpose {currdiv_1, newdiv_1}, p -> p_0 < p_1) then continue
            else {newdiv} | c
            )
        )
    )
tvbPosetChains = memoize tvbPosetChains

tvbChernClass ToricVectorBundleNew := E -> (
    D := weilDecoration E;
    r := rank E;
    sum flatten for i to r-1 list (
        ichains := tvbPosetChains(D,i);
        for c in ichains list (-1)^i * (last c)_0 * (first c)_1
        )
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
