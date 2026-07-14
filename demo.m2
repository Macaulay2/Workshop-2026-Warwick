M2
needsPackage "ToricVectorBundles";

weilDecoration = (V) -> (
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

Y=toricProjectiveSpace 2;
V=tangentBundle Y; displayFiltrations V
w1=weilDecoration V

V2=V ++ lineBundle Y_0 ++ lineBundle (Y_0+3*Y_2); displayFiltrations V2
w2=weilDecoration V2

-- Update on image and kernel
X = toricProjectiveSpace 3
TX = tangentBundle X; details TX
triv = trivialBundle(X,1);

sumoflbs = lineBundle X_0 ++ lineBundle X_1 ++ lineBundle X_2 ++ lineBundle X_3;
f = map(sumoflbs,triv,matrix(QQ,{{1},{1},{1},{1}})); f.map
isWellDefined f
isInjective f
g = map(TX,sumoflbs, transpose sub(matrix rays X,QQ)); g.map
isWellDefined g
isSurjective g
-- New things 
Kg = kernel g; displayFiltrations Kg
If = image f; displayFiltrations If
areIsomorphic(Kg,If)

toricDivisor({1,0,3},Y)