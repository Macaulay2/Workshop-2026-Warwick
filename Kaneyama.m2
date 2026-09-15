---------------------------------------
-- KANEYAMA
---------------------------------------
ToricVectorBundleKaneyama = new Type of HashTable
ToricVectorBundleKaneyama.synonym = "vector bundle on a toric variety using Kaneyama's description"
globalAssignment ToricVectorBundleKaneyama

-- contructors for a Kaneyama type toric vector bundles

--   INPUT  : '(k,F)', a strictly positive integer 'k' and a pure and full dimensional fan 'F'
--   OUTPUT : A ToricVectorBundleKaneyama
toricVectorBundleKaneyama  = method(TypicalValue => ToricVectorBundleKaneyama)
toricVectorBundleKaneyama (ZZ,Fan) := (k,F) -> (
    --Checking for input errors
    if k < 0 then error("The vector bundle must have positive rank.");
    if not isComplete F then error("The fan has to be complete.");
    if not isPointed F then error("The fan has to be pointed.");
    -- Writing the table of Cones of maximal dimension
    n := dim F;
    Frays := rays F;
    Flineality := linealitySpace F;
    topConeTable := customConeSort apply(maxCones F, c-> (Frays_c, Flineality));
    topConeTable = apply(#topConeTable, i -> topConeTable#i => i);
    topConeTable = hashTable topConeTable;

    -- Saving the index pairs of top dimensional Cones that intersect in a codim 1 Cone
     Ltable := hashTable {};
     scan(pairs topConeTable, (C,a) -> Ltable = merge(Ltable,hashTable apply(facesAsCones(1,posHull C), e -> (rays e, linealitySpace e) => a),(b,c) -> if b < c then (b,c) else (c,b)));
     Ltable = hashTable flatten apply(pairs Ltable, p -> if instance(p#1,Sequence) then p#1 => p#0 else {});
     -- Removing Cones on the "border" of F, which have only 1 index
     pairlist := sort keys Ltable;
     -- Saving the identity into the Table of transition matrices
     baseChangeTable := hashTable apply(pairlist, p -> p => map(QQ^k,QQ^k,1));
     -- Saving 0 degrees into the degree table
     degreeTable := hashTable apply(keys topConeTable, C -> C => map(ZZ^n,ZZ^k,0));
     -- Making the vector bundle
     new ToricVectorBundleKaneyama from {
	  "degreeTable" => degreeTable,
	  "baseChangeTable" => baseChangeTable,
	  "codim1Table" => Ltable,
	  "ToricVariety" => F,
	  "number of affine charts" => #topConeTable,
	  "dimension of the variety" => n,
	  "rank of the vector bundle" => k,
	  "topConeTable" => topConeTable,
	  symbol cache => new CacheTable})

--   INPUT : '(k,F,degreeList,matrixList)',  a strictly positive integer 'k', a pure and full dimensional
--                     Fan 'F' of dimension n, a list 'degreeList' of k by n matrices over ZZ, one for each 
--     	    	       top dimensional Cone in 'F' where the columns give the degrees of the generators in the 
--     	    	       corresponding affine chart to this Cone, and a list 'matrixList' of  k by k matrices 
--     	    	       over QQ, one for each pair of top dimensional Cones intersecting in a common codim 1 face. 
--  OUTPUT : The ToricVectorBundleKaneyama 'tvb' 
-- COMMENT : Note that the top dimensional cones are numbered starting with 0 and the codim 1 intersections are 
--           labelled by pairs (i,j) denoting the two top dim cones involved, with i<j and they are ordered
--     	     in lexicographic order. So the matrices in 'matrixList' will be assigned to the pairs (i,j) in that 
--     	     order, where the matrix A assigned to (i,j) denotes the transition
--     	    	 (e_i^1,...,e_i^k) = (e_j^1,...,e_j^k)* A
--     	     The matrices in 'degreeList' will be assigned to the cones in the order in which they are numbered.
toricVectorBundleKaneyama (ZZ,Fan,List,List) := (k,F,degreelist,matrixlist) -> (
     -- Generating the trivial vector bundle of rank k
     tvb := toricVectorBundleKaneyama(k,F);
     -- Adding the given degrees and transition matrices
     tvb = addDegrees(tvb,degreelist);
     tvb = addBaseChange(tvb,matrixlist);
     tvb)

-- Modifying the standard output for a ToricVectorBundleKaneyama to give an overview of its characteristica
net ToricVectorBundleKaneyama := tvb -> ( horizontalJoin flatten ( 
	  "{", 
	  -- prints the parts vertically
	  stack (horizontalJoin \ sort apply({"dimension of the variety",
			                      "rank of the vector bundle",
					      "number of affine charts"}, key -> (net key, " => ", net tvb#key))),
	  "}" ))
 
------------------------------------------
 -- GETTER FUNCTIONS KANEYAMA
 ------------------------------------------

rank ToricVectorBundleKaneyama := T -> T#"rank of the vector bundle"

rays ToricVectorBundleKaneyama := {} >> o -> tvb -> raySortOfFan tvb#"ToricVariety"

 --there was no getter for the ring, could add?

 details ToricVectorBundleKaneyama := tvb -> (
     hashTable apply(pairs(tvb#"topConeTable"), p -> ( p#1 => (rays posHull p#0,tvb#"degreeTable"#(p#0)))),tvb#"baseChangeTable")

maxCones ToricVectorBundleKaneyama := T -> (
      TV := T#"ToricVariety";
      TR := rays TV;
      TL := linealitySpace TV;
      mC := maxCones TV;
      sort apply(mC, c -> posHull(TR_c, TL))
    -- sort maxCones T#"ToricVariety"
   )

--------------------------------------------
-- CONSTRUCT AND MODIFY KANEYAMA
--------------------------------------------

-- PURPOSE : Changing the transition matrices of a given ToricVectorBundle to those given in the List 
--   INPUT : '(tvb,L)',  a ToricVectorBundle 'tvb' and a list 'L'of k by k matrices over QQ, one for each 
--     	    	      	   	  pair of top dimensional Cones intersecting in a common codim 1 face. 
--  OUTPUT : The ToricVectorBundle 'tvb' 
-- COMMENT : Note that the ToricVectorBundle already has a list of pairs (i,j) denoting the codim 1 intersections 
--     	     of two top dim cones, with i<j and they are ordered in lexicographic order. So the matrices in 'L'
--     	     will be assigned to the pairs (i,j) in that order, where the matrix A assigned to (i,j) denotes the 
--     	     transition
--     	    	 (e_i^1,...,e_i^k) = (e_j^1,...,e_j^k)* A

addBaseChange = method(TypicalValue => ToricVectorBundleKaneyama)
addBaseChange (ToricVectorBundleKaneyama,List) := (tvb,L) -> (
     -- Extracting data out of tvb
     pairlist := sort keys tvb#"baseChangeTable";
     k := tvb#"rank of the vector bundle";
     -- Checking for input errors
     if #pairlist != #L then error("Expected the number of matrices to match the number of codim 1 Cones.");
     baseChangeTable := hashTable apply(#pairlist, i -> ( 
	       M := L#i;
	       -- Checking for more input errors
	       if not instance(M,Matrix) then error("Expected the transition matrices to be given as rank times rank matrices.");
	       if numColumns M != k or numRows M != k then error("Expected the base change matrices to be k by k matrices.");
	       if det M == 0 then error("The base change matrices must be invertible.");
	       R := ring source M;
	       M = if R === ZZ or R === QQ then promote(M,QQ) else error("Expected base change over ZZ or QQ");
	       -- Inserting the matrix at the i-th position
	       pairlist#i => M));
     -- Writing the new transition matrices into the bundle
     new ToricVectorBundleKaneyama from {
	  "degreeTable" => tvb#"degreeTable",
	  "baseChangeTable" => baseChangeTable,
	  "ToricVariety" => tvb#"ToricVariety",
	  "number of affine charts" => tvb#"number of affine charts",
	  "dimension of the variety" => tvb#"dimension of the variety",
	  "rank of the vector bundle" => k,
	  "codim1Table" => tvb#"codim1Table",
	  "topConeTable" => tvb#"topConeTable",
	  symbol cache => new CacheTable})

-- PURPOSE : Changing the degrees of the local generators of a given ToricVectorBundleKaneyama to those given in the List 
--   INPUT : '(tvb,L)',  a ToricVectorBundleKaneyama 'tvb' and a list 'L'of n by k matrices over ZZ, one for each 
--     	    	      	 top dimensional Cone. 
--  OUTPUT : The ToricVectorBundleKaneyama 'tvb' 
-- COMMENT : Note that in the ToricVectorBundleKaneyama the top dimensional Cones are already numbered and that the degree
--     	     matrices will be assigned to the Cones in that order. 
addDegrees = method(TypicalValue => ToricVectorBundleKaneyama)
addDegrees (ToricVectorBundleKaneyama,List) := (tvb,L) -> (
     -- Extracting data out of tvb
     tCT := customConeSort keys tvb#"degreeTable";
     k := tvb#"rank of the vector bundle";
     n := tvb#"dimension of the variety";
     -- Checking for input errors
     if #tCT != #L then error("Number of degree matrices must match the number of top dim cones.");
     degreeTable := hashTable apply(#tCT, i -> ( 
	       M := L#i;
	       -- Checking for more input errors
	       if not instance(M,Matrix) then error("The degrees must be given as dimension times rank matrices.");
	       if ring M =!= ZZ then error("Expected the degrees to be in the ZZ lattice.");
	       if numColumns M != k then error("The number of degrees must match the vector bundle rank.");
	       if numRows M != n then error("The degrees must have the dimension of the underlying toric variety.");
	       -- Inserting the degree matrix
	       tCT#i => M));
     -- Writing the new degree table into the bundle
     new ToricVectorBundleKaneyama from {
	  "degreeTable" => degreeTable,
	  "baseChangeTable" => tvb#"baseChangeTable",
	  "ToricVariety" => tvb#"ToricVariety",
	  "number of affine charts" => tvb#"number of affine charts",
	  "dimension of the variety" => n,
	  "rank of the vector bundle" => k,
	  "codim1Table" => tvb#"codim1Table",
	  "topConeTable" => tvb#"topConeTable",
	  symbol cache => new CacheTable})

-- PURPOSE : Checking if the ToricVectorBundleKaneyama is well-defined. Combining previous cocycleCheck and regCheck
--	    First checks if tvb fulfills the cocycle condition
--	    Then checks that tvb satisfies the regularity conditions of the degrees
--   INPUT : 'tvb', a ToricVectorBundleKaneyama
--  OUTPUT : 'true' or 'false'
-- COMMENT : ToricVectorBundles generated by tangentBundle should fulfill the conditions of
--           the regularity check automatically

isWellDefined ToricVectorBundleKaneyama := Boolean => ( tvb -> (
	  -- ORIGINALLY coCycleCheck
	  -- Extracting data out of tvb
     	  n := tvb#"dimension of the variety";
     	  k := tvb#"rank of the vector bundle";
     	  bCT := tvb#"baseChangeTable";
     	  topCones := customConeSort keys tvb#"topConeTable";
     	  L := hashTable {};
     	  -- For each codim 2 Cone computing the list of topCones which have this Cone as a face
     	  -- and save the list of indices of these topCones as an element in L
     	  for i from 0 to #topCones - 1  do L = merge(hashTable apply(facesAsCones(2,posHull topCones#i), C -> (rays C, linealitySpace C) => {i}),L,(a,b) -> sort join(a,b));
     	  -- Finding the cyclic order of every list of topCones in L and write this cyclic order as a 
     	  -- list of consecutive pairs
     	  L = for l in values L list (
	       pairings := {};
	       start := l#0;
	       a := start;
	       l = drop(l,1);
	       i := position(l, e -> dim intersection(posHull topCones#a, posHull topCones#e) == n-1);
	       while i =!= null do (
		    pairings = pairings | {(a,l#i)};
		    a = l#i;
		    l = drop(l,{i,i});
		    i = position(l, e -> dim intersection(posHull topCones#a, posHull topCones#e) == n-1));
	       if dim intersection(posHull topCones#a, posHull topCones#start) == n-1 then pairings | {(a,start)} else continue);
     	  -- Check for every cyclic order of topCones if the product of the corresponding transition
     	  -- matrices is the identity
		  if not (all(L, l -> product apply(reverse l, e -> if e#0 > e#1 then inverse bCT#(e#1,e#0) else bCT#e) == map(QQ^k,QQ^k,1))) then (
		      if debugLevel > 0 then
			  << "--toric vector bundle does not fulfill cocycle condition" << endl;
			return false
		  	);

	  -- ORIGINALLY regcheck
     	  -- Extracting the necessary data
     	  tCT := customConeSort keys tvb#"topConeTable";
     	  c1T := tvb#"codim1Table";
     	  dT := tvb#"degreeTable";
     	  if not (all(keys bCT, p -> (
	       	    -- Taking a pair corresponding to a codim 1 cone, the corresponding transition matrix and its inverse
	       	    A := bCT#p;
	       	    B := inverse A;
	       	    -- Computing the dual of the codim 1 cone
	       	    C := dualCone posHull c1T#p;
	       	    -- Check for all pairs of degree vectors of the two top Cones the reg condition
	       	    all(k, i -> (
			      ri := (dT#(tCT#(p#1)))_{i};
			      all(k, j -> (
				   	rj := (dT#(tCT#(p#0)))_{j};
				   	(if A^{i}_{j} != 0 then contains(C,rj-ri) else true) and (if A^{j}_{i} != 0 then contains(C,ri-rj) else true)))))))) then (
                                             if debugLevel > 0 then
					     << "--toric vector bundle does not satisfy regularity conditions of the degrees" << endl;
		                            return false
					);
		  return true
))



----------------------------------------------------------------------------
-- OPERATIONS ON TORIC VECTOR BUNDLES KANEYAMA
----------------------------------------------------------------------------

ToricVectorBundleKaneyama.directSum = args -> (
     args = toList args;
     T := args#0;
     scan(drop(args,1), E -> T = T ++ E);
     T)

ToricVectorBundleKaneyama ++ ToricVectorBundleKaneyama := (tvb1,tvb2) -> (
    -- Checking for input errors
    if tvb1#"ToricVariety" != tvb2#"ToricVariety" then error("Expected the bundles to be over the same toric variety.");
    -- Extracting data out of tvb1 and tvb2
    k1 := tvb1#"rank of the vector bundle";
    k2 := tvb2#"rank of the vector bundle";
    
    -- Generating the trivial bundle of dimension k1+k2
    E := toricVectorBundleKaneyama(k1 + k2,tvb1#"ToricVariety");
    -- Computing the new degree table and transition matrices and writing the degrees and transition matrices into the bundle
    E = new ToricVectorBundleKaneyama from {
        "degreeTable" => merge(tvb1#"degreeTable",tvb2#"degreeTable", (a,b) -> a|b),
	"baseChangeTable" => merge(tvb1#"baseChangeTable",tvb2#"baseChangeTable", (a,b) -> a++b),
	"ToricVariety" => E#"ToricVariety",
	"number of affine charts" => E#"number of affine charts",
	"dimension of the variety" => E#"dimension of the variety",
	"rank of the vector bundle" => k1 + k2,
	"codim1Table" => E#"codim1Table",
	"topConeTable" => E#"topConeTable",
	symbol cache => new CacheTable};

    -- we combined regCheck and cocycleCheck into isWellDefined.....should we change these and remove them then?
     if (tvb1.cache.?regCheck and tvb2.cache.?regCheck and tvb1.cache.regCheck and tvb2.cache.regCheck and (
	       tvb1.cache.?cocycle and tvb2.cache.?cocycle and tvb1.cache.cocycle and tvb2.cache.cocycle)) then (
	  E.cache.regCheck = true;
	  E.cache.cocycle = true);
     E   
    )

dual ToricVectorBundleKaneyama := {} >> opts -> tvb -> (
    -- Inverting the degrees and the transition matrices
    degreeTable := hashTable apply(pairs tvb#"degreeTable", p -> p#0 => -(p#1));
    baseChangeTable := hashTable apply(pairs tvb#"baseChangeTable", p -> p#0 => transpose inverse p#1);
    -- Writing the inverted tables into the bundle
    E := new ToricVectorBundleKaneyama from {
        "degreeTable" => degreeTable,
        "baseChangeTable" => baseChangeTable,
        "ToricVariety" => tvb#"ToricVariety",
        "number of affine charts" => tvb#"number of affine charts",
        "dimension of the variety" => tvb#"dimension of the variety",
        "rank of the vector bundle" => tvb#"rank of the vector bundle",
        "codim1Table" => tvb#"codim1Table",
        "topConeTable" => tvb#"topConeTable",
         symbol cache => new CacheTable};
        if tvb.cache.?regCheck and tvb.cache.regCheck and tvb.cache.?cocycle and tvb.cache.cocycle then (
            E.cache.regCheck = true;
            E.cache.cocycle = true);
        E)

-- PURPOSE : Compute the Euler characteristic
--   INPUT : '(u,T)',  where 'T' is a ToricVectorBundleKaneyama and 'u' is a one column matrix over ZZ giving a degree vector
--  OUTPUT : The Euler characteristic of the Cech complex at degree 'u'
eulerChi (Matrix,ToricVectorBundleKaneyama) := (u,T) -> (
    if not T.cache.?eulerChi then T.cache.eulerChi = new MutableHashTable;
    if not T.cache.eulerChi#?u then (
	  n := T#"dimension of the variety";
	  -- Compute the Cech complex and compute the alternating sum of the dimensions
	  T.cache.eulerChi#u = sum apply(n+2, i -> (-1)^i * numColumns (cechComplex(i,T,u))#1));
     T.cache.eulerChi#u)

--   INPUT : 'T',  a ToricVectorBundleKaneyama
--  OUTPUT : The Euler characteristic of the bundle
eulerChi ToricVectorBundleKaneyama := T -> (
     -- Compute the set of degrees with possible cohomology
     L := latticePoints deltaE T;
     -- Sum up their characteristics
     sum apply(L, l -> eulerChi(l,T)))

-- PURPOSE : Returning the table of codimension 1 cones of the underlying fan
--   INPUT : 'T',  a ToricVectorBundleKaneyama
--  OUTPUT : a HashTable
codim1Table = method(TypicalValue => HashTable)
codim1Table ToricVectorBundleKaneyama := T -> T#"codim1Table"

--Q: Why do they send cohomology to a ''not public'' function cohom? Should I keep it like this or just use cohomology?
--I'm going to just use cohomology for now.....

-- PURPOSE : Computing the cohomology of a given ToricVectorBundleKaneyama
--   INPUT : '(k,T,u)',  'k' for the 'k'th cohomology group, 'T' a ToricVectorBundleKaneyama, and 'u' the degree
--  OUTPUT : 'ZZ',	     the dimension of the degree 'u' part of the 'k'th cohomology group of 'tvb'
cohomology (ZZ,ToricVectorBundleKaneyama,Matrix) := opts -> (k,T,u) -> (
     if not T.cache.?HH then T.cache.HH = new MutableHashTable;
     if not T.cache.HH#?(k,u) then (
	  -- Get the k-1 th and k th differential
	  d := if k == 0 then rank ker (cechComplex(k,T,u))#1 else (
	       -- Generate the two boundary operators
	       d1 := (cechComplex(k-1,T,u))#1;
	       d2 := (cechComplex(k,T,u))#1;
	       (rank ker d2) - (rank image d1));
	  T.cache.HH#(k,u) = (ring T)^(toList(d:flatten entries(-u))));
     T.cache.HH#(k,u))

--   INPUT : '(i,T,P)',  'i' for the 'i'th cohomology group, 'T' a ToricVectorBundleKaneyama, and 'P' a list of degrees
--  OUTPUT : 'List',	     the list of the graded modules of the corresponding degree parts of the cohomology group which are non zero
cohomology(ZZ,ToricVectorBundleKaneyama,List) := opts -> (i,T,P)-> (
     if opts.Degree == 1 then print ("Number of degrees to calculate: "|(toString(#P)));
     for j in P list (
	  if opts.Degree == 1 then << "." << flush;
	  j = cohomology(i,T,j);
	  if j != 0 then j else continue))

--   INPUT : '(i,T)',  'i' for the 'i'th cohomology group, 'T' a ToricVectorBundleKaneyama
--  OUTPUT : the group as a graded module where the generators have the corresponding degree of the weight vector
-- COMMENT : if the option "Degree" => 1 is given then it displays the number of degrees to calculate
cohomology(ZZ,ToricVectorBundleKaneyama) := opts -> (i,T)-> (
     L := cohomology(i,T,latticePoints deltaE T,Degree => opts.Degree);
     if L == {} then (ring T)^0 else directSum L)

-- PURPOSE : Computing the rank of the cohomology group of a given ToricVectorBundleKaneyama
--   INPUT : '(i,T)',  'i' for the 'i'th cohomology group, 'T' a ToricVectorBundleKaneyama
--  OUTPUT : 'ZZ',  the rank of the 'i'th cohomology group
hh(ZZ,ToricVectorBundleKaneyama) := ZZ => (i,T) -> rank cohomology(i,T)

-- PURPOSE : Computing the polytope deltaE in the degree space such that outside this polytope
--     	     every cohomology is 0 
--   INPUT : 'tvb',  a ToricVectorBundleKaneyama
--  OUTPUT : a Polyhedron
deltaE ToricVectorBundleKaneyama := (cacheValue symbol deltaE)( tvb -> (
     	  if not isComplete tvb#"ToricVariety" then error("The toric variety needs to be complete.");
     	  n := tvb#"dimension of the variety";
      
	  -- Extracting necessary data
          raylist := rays tvb;
          rl := #raylist;
          k := tvb#"rank of the vector bundle";
          tCT := keys tvb#"topConeTable";
          dT := tvb#"degreeTable";
          -- Creating an index table, for each ray the first top cone containing it
          raytCTindex := hashTable apply(#raylist, r -> r => position(tCT, C -> contains(posHull C_0,raylist#r)));
          raylist = transpose matrix {raylist};
          -- Get the subsets of 'n' elements in 'rl'
          sset := subsets(rl,n);
          jList := {{}};
          -- Get all different combinations of choices of variety dimension many degree vectors
          for i from 0 to n-1 do jList = flatten apply(jList, l -> apply(k, j -> l|{j}));
          M := map(QQ^1,QQ^n,0);
          v := map(QQ^1,QQ^1,0);
          -- For every 'n' in 'l' subset and any combination in jList get the intersection of the dual cones
          -- of the corresponding rays. If this is a non-empty compact polytope then add the vertices to the
          -- list L
     	       L := unique flatten apply(sset, s -> (
	       	    	 unique for j in jList list (
		    	      N := matrix apply(n, i -> {raylist^{s#i},raylist^{s#i} * ((dT#(tCT#(raytCTindex#(s#i))))_{j#i})});
		    	      w := N_{n};
		    	      N = submatrix'(N,{n});
		    	      P := polyhedronFromHData(M,v,N,w);
		    	      if isCompact P and (not isEmpty P) then vertices P else continue)));
     	       -- Make a matrix of all the vertices in L
     	       M = matrix {L};
     	       convexHull M))

-- PURPOSE : Returning the underlying fan of a toric vector bundle
--   INPUT : 'T',  a ToricVectorBundleKaneyama
--  OUTPUT : a Fan
fan ToricVectorBundleKaneyama := T -> T#"ToricVariety"

-- PURPOSE : Checking if two toric vector bundles (Kaneyama) are equal
--   INPUT : '(tvb1,tvb2)',  two ToricVectorBundleKaneyama
--  OUTPUT : 'true' or 'false' 
ToricVectorBundleKaneyama == ToricVectorBundleKaneyama := (tvb1,tvb2) -> tvb1 === tvb2

-- PURPOSE : Computing the tensor product of two toric vector bundles (Kaneyama) over the same Fan
--   INPUT : '(tvb1,tvb2)',  two ToricVectorBundle Kaneyama over the same Fan in the same description
--  OUTPUT : 'tvb',  a ToricVectorBundleKaneyama which is the tensor product in the same description
tensor(ToricVectorBundleKaneyama, ToricVectorBundleKaneyama) := ToricVectorBundleKaneyama => {} >> opts -> (tvb1, tvb2) -> (
    -- Checking for input errors
     if tvb1#"ToricVariety" != tvb2#"ToricVariety" then error("Expected bundles over the same toric variety.");
     k1 := tvb1#"rank of the vector bundle";
     k2 := tvb2#"rank of the vector bundle";

    -- Extracting data out of tvb1 and tvb2
     -- Generating the trivial bundle of dimension k1+k2
     E := toricVectorBundleKaneyama(k1 * k2,tvb1#"ToricVariety");
     -- Computing the new degree table and transition matrices and writing the degrees and transition matrices into the bundle
     E = new ToricVectorBundleKaneyama from {
         "degreeTable" => merge(tvb1#"degreeTable",tvb2#"degreeTable", (a,b) -> matrix {flatten apply(k2, j -> apply(k1, i -> a_{i}+b_{j}))}),
         "baseChangeTable" => merge(tvb1#"baseChangeTable",tvb2#"baseChangeTable", (a,b) -> (
                 matrix flatten apply(k2, j -> apply(k1, i -> flatten apply(k2, j' -> apply(k1, i' -> a_(i,i') * b_(j,j'))))))),
         "ToricVariety" => E#"ToricVariety",
         "number of affine charts" => E#"number of affine charts",
         "dimension of the variety" => E#"dimension of the variety",
         "rank of the vector bundle" => k1 + k2,
         "codim1Table" => E#"codim1Table",
         "topConeTable" => E#"topConeTable",
         symbol cache => new CacheTable};
     if (tvb1.cache.?regCheck and tvb2.cache.?regCheck and tvb1.cache.regCheck and tvb2.cache.regCheck and (
             tvb1.cache.?cocycle and tvb2.cache.?cocycle and tvb1.cache.cocycle and tvb2.cache.cocycle)) then (
         E.cache.regCheck = true;
         E.cache.cocycle = true);
     E

)

ToricVectorBundleKaneyama ** ToricVectorBundleKaneyama := (tvb1,tvb2) -> tensor(tvb1,tvb2)

-- PURPOSE : Generating the Vector Bundle given by a divisor

weilToCartierKaneyama = method();

--   INPUT : '(L,F)',  a list 'L' of weight vectors, one for each ray of the Fan 'F'
--  OUTPUT : 'tvb',  a ToricVectorBundleKaneyama
weilToCartierKaneyama (List,Fan) := opts -> (L,F) -> (
    rl := raySortOfFan F;
    -- Checking for input errors
    if #L != #rl then error("The number of weights has to equal the number of rays.");
    n := ambDim F;

    if not isPure F or ambDim F != dim F then error("Expected the Fan to be pure of maximal dimension.");
    -- Creating 0 matrices to compute intersection of hyperplanes to compute the degrees
    Mfull := matrix {toList(n:0)};
    vfull := matrix {{0}};
    -- Checking for further errors and assigning the weights to the rays
    L = hashTable apply(#rl, i -> (if class L#i =!= ZZ then error("The weights have to be in ZZ."); rl#i => L#i));
    -- Keeping track of the lowest common multiple of denominators of the degrees,
    -- to check whether the divisor itself is Cartier or which multiple
    denom := 1;
    -- Computing the degree vector for every top dimensional cone
    tvb := toricVectorBundleKaneyama(1,F);
    gC := customConeSort keys tvb#"degreeTable";
    gC = apply(gC, C -> (
            rC := (rays posHull C);
            -- Taking the first n x n submatrix
            rC1 := rC_{0..n-1};
            -- Setting up the solution vector by composing the corresponding weights
            v := matrix apply(n, i -> (c := rC1_{i}; {-(L#c)}));
            -- Computing the degree vector
            w := vertices polyhedronFromHData(Mfull,vfull,transpose rC1,v);
            -- Checking if w also fulfils the equations given by the remaining rays
            if numColumns rC != n then (
                v = v || matrix apply(toList(n..(numColumns rC)-1), i -> {-(L#(rC_{i}))});
                if (transpose rC)*w - v != 0 then error("The weights do not define a Cartier divisor."));
            -- Check if w is QQ-Cartier
            scan(flatten entries w, e -> denom = lcm(denominator e ,denom));
            w));
    -- If the divisor is only QQ Cartier, then its replaced by its first Cartier multiple
    if denom != 1 then error("The divisor is only QQ-Cartier, but "|toString(denom)|" times the divisor is Cartier.");
    gC = apply(gC, e -> substitute(denom*e,ZZ));
    -- Construct the actual line bundle
    addDegrees(tvb,gC))

-- PURPOSE : Computing the cotangent bundle on a smooth, pure, and full dimensional Toric Variety 
--   INPUT : 'F',  a smooth, pure, and full dimensional Fan
--  OUTPUT : 'tvb',  a ToricVectorBundleKaneyama

tangentBundleKaneyama = method()
tangentBundleKaneyama Fan := F -> dual cotangentBundleKaneyama F
cotangentBundleKaneyama = method()
cotangentBundleKaneyama Fan := F -> (
     -- Checking for input errors
     if not isSmooth F then error("The Toric Variety has to be smooth.");
     if not isComplete F then error("The Toric Variety has to be complete.");
     if not isPointed F then error("The Fan has to be pointed.");
     -- Generating the trivial bundle of dimension n
     n := dim F;
     tvb := toricVectorBundleKaneyama(n,F);
     tCT := customConeSort keys tvb#"topConeTable";
     pairlist := keys tvb#"baseChangeTable";
     -- Computing the degrees and transition matrices of the cotangent bundle
     degreeTable := hashTable apply(tCT, p -> p => substitute(rays dualCone posHull p,ZZ));
     baseChangeTable := hashTable apply(pairlist, p -> ( p => substitute(inverse(degreeTable#(tCT#(p#1)))*(degreeTable#(tCT#(p#0))),QQ)));
     -- Writing the data into the bundle
     E := new ToricVectorBundleKaneyama from {
	  "degreeTable" => degreeTable,
	  "baseChangeTable" => baseChangeTable,
	  "ToricVariety" => tvb#"ToricVariety",
	  "number of affine charts" => tvb#"number of affine charts",
	  "dimension of the variety" => n,
	  "rank of the vector bundle" => n,
	  "codim1Table" => tvb#"codim1Table",
	  "topConeTable" => tvb#"topConeTable",
	  symbol cache => new CacheTable};
     E.cache.regCheck = true;
     E.cache.cocycle = true;
     E)
 
-- PURPOSE : Computing the Cech complex of a vector bundle (Kaneyama)
--   INPUT : '(k,T,u)', where 'k' is an integer between -1 and the dimension of the bundle +1, 'T' a ToricVectorBundleKaneyama, and 'u' a
--     	    	        one column matrix giving a degree vector
--  OUTPUT : '(Fk,Fkcolumns,FktoFk+1)', where 'Fk' is a hashTable with the summands of the 'k'th chain, 'Fkcolumns' is a hashTable with the
--     	    	      	   	        dimensions of these summands, and 'FktoFk+1' is a hashTable with the components of the 'k'th 
--     	    	      	   	        boundary operator
cechComplex (ZZ,ToricVectorBundleKaneyama,Matrix) := (k,tvb,u) -> ( 
     -- Checking for input errors
     if numRows u != tvb#"dimension of the variety" or numColumns u != 1 then error("Expected a matrix with 1 column and ", toString tvb#"dimension of the variety", " rows.");
     if ring u =!= ZZ then error("The degree has to be an integer vector.");
     if k < 0 or tvb#"dimension of the variety"+1 < k then error("k has to be between 0 and the variety dimension for the k-th cohomology.");
     -- For a given space F1 at chain k in the filtration together with the degree vector 'u' and the information of the bundle this auxiliary 
     -- function computes the boundary operator to the next chain (k+1) which is F1toF2, the dimensions of the summands of 'F1' in 'F1columns' 
     -- and the next chain 'F2'
     makeNewDiffAndTarget := (M1,rk,l,tCT,bCT,dT) -> (
	  -- Recursive function that finds a path over codim 1 cones from one topdim cone ('i') to another ('j')
     	  -- using the steps in 'pl'
     	  findpath := (i,j,pl) -> (
	       -- Recursive function finds a path from the actual cone 'i' to the Cone 'j' using the steps in 'pl'
	       -- where 'cl' is the  sequence of steps taken so far from the original 'i' and 'minpath' is the 
	       -- shortest path found so far
	       findrecursive := (i,j,pl,cl,minpath) -> (
	       	    -- If the last step from 'i' to 'j' is part of 'pl' then add '(i,j)' to 'cl'
	       	    if member((i,j),pl) or member((j,i),pl) then (
		    	 cl = append(cl,(i,j));
		    	 -- Check if the new found path is shorter than shortest so far
		    	 if #cl < #minpath or minpath == {} then minpath = cl)
	       	    -- otherwise find a path with the remaining steps in 'pl'
	       	    else (
		    	 L1 := {};
		    	 L2 := {};
		    	 -- Sort the remaining possible steps into those containing 'i'in 'L1' and those who not in 'L2'
		    	 for e in pl do if member(i,e) then L1 = append(L1,e) else L2 = append(L2,e);
		    	 -- Call findrecursive for each step in 'L1', with new starting cone the other index in the pair and new 
		    	 -- remaining pairs list 'L2' and add the step to 'cl'
		    	 for e in L1 do ( 
			      if e#0 == i then minpath = findrecursive(e#1,j,L2,append(cl,e),minpath)
			      else minpath = findrecursive(e#0,j,L2,append(cl,(e#1,e#0)),minpath)));
	       	    minpath);
	       -- Start with an empty sequence of steps, no minimal path yet and all possible stepsd
	       cl := {};
	       minpath := {};
	       findrecursive(i,j,pl,cl,minpath));
	  M2 := {};
	  for p in pairs M1 do (
	       L := select(toList(0..rk-1), i -> not member(i,p#1#0));
	       for i from last(p#0)+1 to l-1 do (
		    cl := append(p#0,i);
		    C := intersection(posHull p#1#1, posHull tCT#i);
		    degs := dT#(tCT#(cl#0));
		    M2 = append(M2,cl => (sort unique join(p#1#0,select(L, i -> contains(dualCone C,u- degs_{i}))),(rays C, linealitySpace C)))));
	  M2 = hashTable M2;
	  -- Constructing the zero map over QQ
     	  d1 := map(QQ^0,QQ^0,0);
     	  -- Constructing the matrix of the sequence for the cohomology
	  scan(pairs M1, (a,b) -> (
		    b = b#0;
		    -- 'A' will be a column of the matrix d1 of the sequence
		    A := map(QQ^0,QQ^(#b),0);
		    -- One intersection in M1 is selected, by going through the intersections in M2 we get the first "column" of block matrices in A 
		    -- by looking at the images in all intersections in M2
		    scan(pairs M2, (c,d) -> (
			      -- Only if the intersection is made by intersecting with one more cone, the resulting matrix has to be computed, 
			      -- because otherwise it is automatically zero
			      if isSubset(a,c) then (
				   -- get the signum by looking at the position the new cone is inserted
				   signum := (-1)^(#c - position(c, e -> not member(e,a)) - 1);
				   i := a#0;
				   j := c#0;
				   -- if i == j then no base change between the two representations has to be made, so the submatrix of the 
				   -- identity inserting the positions of the degrees 'b' into the degrees 'd' is added in this column
				   if i == j then A = A || (signum * (map(QQ^rk,QQ^rk,1))_b)
				   -- Otherwise we have to find the transition matrix from cone 'i' to Cone 'j'
				   else (
					-- find the transition matrix
					mpath := findpath(i,j,keys bCT);
					-- If the path has one element then we take the 'b'-'d' part of that matrix, otherwise the multiplication 
					-- of the matrices corresponding to the steps in the path and add the path as a new step with corresponding matrix
					if #mpath == 1 then (
					     if i < j then A = A || (signum * (bCT#(i,j))_b)
					     else A = A || (signum * (inverse (bCT#(j,i)))_b))
					else (
					     A1 := map(QQ^rk,QQ^rk,1);
					     for p in mpath do (
						  if p#0 < p#1 then A1 = bCT#p * A1
						  else A1 = (inverse bCT#(p#1,p#0))*A1);
					     if i < j then bCT = hashTable join(apply(pairs bCT, ps -> ps#0 => ps#1), {(i,j) => A1})
					     else bCT = hashTable join(apply(pairs bCT, ps -> ps#0 => ps#1), {(j,i) => inverse A1});
					     A = A || (signum * A1_b))))
			      else (
				   A = A || map(QQ^rk,QQ^(#b),0))));
		    -- Adding the new column to d1
		    if d1 == map(QQ^0,QQ^0,0) then d1 = A
		    else d1 = d1 | A));
	  (d1,M2));
     if not tvb.cache.?cech then tvb.cache.cech = new MutableHashTable;
     rk := tvb#"rank of the vector bundle";
     l := tvb#"number of affine charts";
     tCT := customConeSort keys tvb#"topConeTable";
     bCT := tvb#"baseChangeTable";
     dT := tvb#"degreeTable";
     if not tvb.cache.cech#?(k,u) then (
     	  if k == 0 then (
	       M20 := hashTable apply(subsets(l,k+1), cl -> (
		    	 C := intersection apply(cl, i -> posHull tCT#i);
		    	 degs := dT#(tCT#(cl#0));
		    	 L := select(toList(0..rk-1), i -> contains(dualCone C,u - degs_{i}));
		    	 cl => (L,(rays C, linealitySpace C))));
	       (d20,M30) := makeNewDiffAndTarget(M20,rk,l,tCT,bCT,dT);
	       tvb.cache.cech#(k,u) = (M20,d20);
	       tvb.cache.cech#(k+1,u) = M30)
	  else (
	       M1 := if not tvb.cache.cech#?(k-1,u) then (
	       	    hashTable apply(subsets(l,k), cl -> (
		    	      C := intersection apply(cl, i -> posHull tCT#i);
		    	      degs := dT#(tCT#(cl#0));
		    	      L := select(toList(0..rk-1), i -> contains(dualCone C,u - degs_{i}));
		    	      cl => (L,(rays C, linealitySpace C))))) else tvb.cache.cech#(k-1,u);
	       (d1,M2) := makeNewDiffAndTarget(M1,rk,l,tCT,bCT,dT);
	       (d2,M3) := makeNewDiffAndTarget(M2,rk,l,tCT,bCT,dT);
	       tvb.cache.cech#(k-1,u) = (M1,d1);
	       tvb.cache.cech#(k,u) = (M2,d2);
	       tvb.cache.cech#(k+1,u) = M3))
     else if not instance(tvb.cache.cech#(k,u),Sequence) then (
	  M21 := tvb.cache.cech#(k,u);
	  (d21,M31) := makeNewDiffAndTarget(M21,rk,l,tCT,bCT,dT);
	  tvb.cache.cech#(k,u) = (M21,d21);
	  tvb.cache.cech#(k+1,u) = M31);
     tvb.cache.cech#(k,u))
---------------------------------------------------------------
-- AUXILIARY FUNCTIONS FOR KANEYAMA
---------------------------------------------------------------
