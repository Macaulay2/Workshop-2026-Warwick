--*- coding: utf-8 -*-
---------------------------------------------------------------------------
-- UPDATE HISTORY : November 2008, November 2009, April 2010, May 2024, April 2025, September 2026
---------------------------------------------------------------------------
newPackage("ToricVectorBundles",
    Headline => "vector bundles on toric varieties",
    Version => "2.0",
    Date => "September, 2026",
    Authors => {
        {Name => "René Birkner"},
        {Name => "Adrian Cook",
         Email => "a.cook@ed.ac.uk"},
        {Name => "Mayo Mayo Garcia",
         HomePage => "https://warwick.ac.uk/fac/sci/maths/people/staff/garcia/",
         Email => "mayo.mayo-garcia@warwick.ac.uk"},
        {Name => "Nathan Ilten",
         HomePage => "https://www.sfu.ca/~nilten/",
         Email => "nilten@sfu.ca"},
        {Name => "Julia McClellan",
         Email => "julia.mcclellan@queensu.ca"},
        {Name => "Marco Fava",
         HomePage => "https://sites.google.com/view/marco-fava/home-page",
         Email => "marco.fava@warwick.ac.uk"},
        {Name => "Labix Liu",
         HomePage => "https://labix-liu.github.io/",
         Email => "sin.liu@qmul.ac.uk"},
        {Name => "Lars Petersen"},
        {Name => "Sasha Zotine",
         HomePage => "https://sites.google.com/view/szotine/home",
         Email => "sashahbc@gmail.com"},
        },
    Keywords => {"Toric Geometry"},
    Certification => {
        "journal name" => "The Journal of Software for Algebra and Geometry: Macaulay2",
        "journal URI" => "https://msp.org/jsag/",
        "article title" => "Computations with equivariant toric vector bundles",
        "acceptance date" => "2010-06-15",
        "published article URI" => "https://msp.org/jsag/2010/2-1/p03.xhtml",
        "published article DOI" => "10.2140/jsag.2010.2.11",
        "published code URI" => "https://msp.org/jsag/2010/2-1/jsag-v2-n1-x03-code.zip",
        "release at publication" => "314a1e7a1a5f612124f23e2161c58eabeb491f46",
        "version at publication" => "1.0",
        "volume number" => "2",
        "volume URI" => "https://msp.org/jsag/2010/2-1/"
        },
    Configuration => {},
    PackageImports => {"Varieties"},
    PackageExports => {"Isomorphism", "Polyhedra", "NormalToricVarieties"},
    DebuggingMode => true
    )

---------------------------------------------------------------------------
-- COPYRIGHT NOTICE:
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see <http://www.gnu.org/licenses/>.
--
---------------------------------------------------------------------------

export {
    -- Types
    "ToricVectorBundle",
    "ToricVectorBundleKaneyama",
    "ToricVectorBundleMap",
    -- Constructors
    "cotangentBundleKaneyama",
    "lineBundle",
    "tangentBundleKaneyama",
    "toricVectorBundle",
    "trivialBundle",
    "toricVectorBundleKaneyama",
    -- Getters
    "filtrationMatrices",
    "filtrationJumps",
    "strata",
    -- Operations
    "areIsomorphic",
    "cechComplexKaneyama",
    "deltaE",
    "deltaEKaneyama",
    "details",
    "detailsKaneyama",
    "filtrations" => "details",
    "eulerChi",
    "eulerChiKaneyama",
    "filteredPiece",
    "moduleToKlyachko",
    "klyachkoToModule",
    "isGeneral",
    "weilDecoration",
    "weilToKlyachko",
    "randomDeformation",
    "twist",
    "isTwistOf",
    "firstChernClass",
    "grRing", -- For test 13
    -- Misc
    "displayFiltrations",
    -- Kaneyama (old code)
    "addBaseChange",
    "addDegrees",
    "cartierIndex",
    "charts",
    "lineBundleKaneyama", 
    "hirzebruchFan",
    "pp1ProductFan", 
    "projectiveSpaceFan",
    "raySortOfFan",
    "customConeSort"
    }

load "Kaneyama.m2"
-- These are cached keywords as part of:
-- cechComplex
protect cech
-- isWellDefined for Kaneyama bundles
protect cocycleCondition
protect regularityCondition
-- areIsomorphic
protect iso
-- cohomology
protect gradedCoeffRing

---------------------------------------------------------------------------
-- MAIN TYPE
---------------------------------------------------------------------------

ToricVectorBundle = new Type of HashTable
ToricVectorBundle.synonym = "vector bundle on a toric variety using Klyachko's description"
globalAssignment ToricVectorBundle

toricVectorBundle = method(Options => true)
toricVectorBundle (NormalToricVariety, List, List) := {} >> o -> (baseVariety, matrixList, indexesList) -> (
    -- error checking
    if #matrixList != #(rays baseVariety) then error("there must be as many filtrations as rays of the base");
    if #indexesList != #(rays baseVariety) then error("there must be as many filtrations as rays of the base");
    L := apply(matrixList, m -> {numColumns m, numRows m});
    if not same L then error("the sizes of the filtration matrices must be the same");
    rankE := (unique flatten L)_0;
    if any(indexesList, l -> #l != rankE) then error("the filtration data must be same length as rank");
    -- technically the filtration matrices need to be over the coefficient ring of E
    modifiedMatList := apply(matrixList, M -> sub(M, coefficientRing ring baseVariety));
    new ToricVectorBundle from {
	symbol variety => baseVariety,
	symbol filtrationMatrices => modifiedMatList,
	symbol filtrationJumps => indexesList,
	symbol rank => rankE,
	symbol cache => new CacheTable}
    )
-- Alternative input
toricVectorBundle (NormalToricVariety, HashTable) := {} >> o -> (baseVariety, filtrationTable) -> (
    if set rays baseVariety != set keys filtrationTable then error("expected values of the hashtable to be the rays of the base");
    (mats, jumps) := toSequence transpose for p in rays baseVariety list toList filtrationTable#p;
    toricVectorBundle(baseVariety, mats, jumps)
    )

---------------------------------------------------------------------------
-- BASIC CONSTRUCTORS
---------------------------------------------------------------------------

trivialBundle = method()
trivialBundle NormalToricVariety := X -> trivialBundle(X,1)
trivialBundle(NormalToricVariety, ZZ) := (X,r) -> (
    if r < 0 then error("expected nonnegative rank.");
    H := hashTable for p in rays X list p => {id_((coefficientRing ring X)^r), toList(r:0)};    
    toricVectorBundle(X, H)
)

lineBundle = method()
lineBundle ToricDivisor := D -> lineBundle(variety D, entries D)
lineBundle(NormalToricVariety, List):= (X, L) ->(
    if #L != #rays X then( error("the list should index a divisor on the base"););
    jumps := for e in L list {e};
    mats := for p in rays X list matrix {{1_(coefficientRing ring X)}};
    toricVectorBundle(X, mats, jumps)
)

cotangentBundle NormalToricVariety := X -> dual tangentBundle X
tangentBundle NormalToricVariety := X -> (
    if not isSmooth X then error("the base toric variety must be smooth");
    R:= coefficientRing ring X;
    raysX := rays X;
    chR := char R;
    -- TODO: decide if this is the way we want to implement it
    if chR != 0 then(
    if not all apply(unique flatten raysX, p -> gcd(chR, p)==1 or p == 0) then( error ("Some entry in the rays is divisible by the characteristic of the field. Please use other method to define the bundle")););
    raylist := apply(raysX, p -> promote(matrix vector p,R));
    -- The filtration matrix for ray rho has rho has the first column, and its
    -- orthogonal complement for the remaining columns.
    filtMats := apply(raylist, p -> p | complement p);
    -- the filtration has rho at index 1, and all other vectors at index 0.
    filtJumps := for p in rays X list {1} | toList((dim X-1):0);
    toricVectorBundle(X,filtMats,filtJumps)
    )

--------------------------------------------------------------
-- GETTER FUNCTIONS FOR TORIC VECTOR BUNDLES
--------------------------------------------------------------

variety ToricVectorBundle := E -> E.variety
fan ToricVectorBundle := E -> fan E.variety
rank ToricVectorBundle := E ->(E.rank)
ring ToricVectorBundle := E -> coefficientRing ring variety E
rays ToricVectorBundle := {} >> o -> E -> rays variety E 

-- This ring is needed for the cohomology computations
grRing = method()
grRing ToricVectorBundle := (cacheValue symbol gradedCoeffRing)(E ->  (ring E)[DegreeRank => dim variety E])

filtrationJumps = method()
filtrationJumps ToricVectorBundle := E -> (E.filtrationJumps)
-- This extracts a specific jump for a ray p. 
filtrationJumps (ToricVectorBundle, List) := (E,p) -> (
    j:= position(rays E, c -> c == p);
    (E.filtrationJumps)_j
)

filtrationMatrices = method()
filtrationMatrices ToricVectorBundle := E -> (E.filtrationMatrices)
-- This extracts a specific filtration matrix for a ray p.
filtrationMatrices(ToricVectorBundle, List) := (E,p) -> (
    j:= position(rays E, c -> c == p);
    (E.filtrationMatrices)_j
)

details = method()
details ToricVectorBundle := tvb ->( 
    raysX := rays tvb;
    filts := filtrationMatrices tvb;
    jumps := filtrationJumps tvb; 
    hashTable for i to #raysX -1 list(raysX_i => {filts_i, jumps_i})
)

filteredPiece = method()
filteredPiece (ToricVectorBundle, List, ZZ) := (E, p, i) ->(
    dataE:= (details(E))#p;
    jumpE:= dataE_1;
    inds:= select(toList(0..rank(E)-1), n -> (i <= jumpE_n));
    (dataE_0)_inds
)

----------------------------------------------------------------------------
-- OPERATIONS ON TORIC VECTOR BUNDLES
----------------------------------------------------------------------------

ToricVectorBundle.directSum = args -> (
    args = toList args;
    T := args#0;
    scan(drop(args,1), E -> T = T ++ E);
    T)      
ToricVectorBundle ++ ToricVectorBundle := (tvb1,tvb2) -> (
    --Errors check
    if variety tvb1 =!= variety tvb2 then(error("expected the bundles to be over the same base toric variety") );
    X := variety tvb1;
    nrays := # rays variety tvb1;
    L1:= filtrationMatrices tvb1; 
    L2:= filtrationMatrices tvb2;
    Lnew:= apply(nrays, i -> L1_i++L2_i);
    J1:= filtrationJumps tvb1; 
    J2:= filtrationJumps tvb2;
    Jnew:= apply(nrays, i -> J1_i|J2_i);
    toricVectorBundle(X, Lnew, Jnew)
    ) 

-- PURPOSE : Computing the dual bundle to a given ToricVectorBundle
--   INPUT : 'tvb',  a ToricVectorBundle
--  OUTPUT : the dual ToricVectorBundle
dual ToricVectorBundle := {} >> opts -> tvb -> (    
    -- if a vector space has basis B, the dual has basis transpose inverse B
    filtMats := apply(filtrationMatrices tvb, M -> transpose inverse M);
    -- the jumps in the filtration get reverse and negated.
    -- TODO check if we need reverse J or not
    filtJumps := apply(filtrationJumps tvb, J -> - J);
    return toricVectorBundle(variety tvb, filtMats, filtJumps)
    )

-- PURPOSE : Computing the 'l'-th exterior power of a ToricVectorBundle
--   INPUT : '(TVB, l)',  where 'l' is a strictly positive integer and 'TVB'is a TorcVectorBundle
--  OUTPUT : the 'l'-th exterior power of TVB
exteriorPower (ToricVectorBundle, ZZ) := opts -> (TVB, l) -> (
    if l < 0 then (
        error("expected nonnegative exponent");
        )
    else if l == 0 then (
        trivialBundle(variety TVB, 1)
        )
    else if l > rank TVB then (
        trivialBundle(variety TVB, 0)
        )
    else (
        R := rays variety TVB;
        fM := filtrationMatrices TVB;
        fJ := filtrationJumps TVB;
        ind := subsets(rank TVB,l);
        indtable := hashTable apply(#ind, i -> ind#i => i);
        newfM := apply(#R, t -> (
                M := mutableMatrix(ring TVB,#ind,#ind);
                for i in ind do (
                    for j in ind do (
                        M_(indtable#i,indtable#j) = det((fM_t)^i_j);
                        );
                    );
                matrix M
                )
            );
        newfJ := apply(#R, t -> (
                apply(ind, j -> sum (fJ_t)_j)
                )
            );
        toricVectorBundle(variety TVB, newfM, newfJ)
        )
    )

-- PURPOSE : Constructs the symmetric power of a given bundle. 
--   INPUT : '(TVB, l)', where "TVB" is a bundle and l is the rank, 
--  OUTPUT : the lth symmetric power of TVB. 
symmetricPower (ToricVectorBundle, ZZ) := (TVB, l) -> (
    if l < 0 then (
        error("expected nonnegative exponent");
        )
    else if l == 0 then (
        trivialBundle(variety TVB, 0)
        )
    else (
        R := rays variety TVB;
        fM := filtrationMatrices TVB;
        fJ := filtrationJumps TVB;
        ind := sort apply(subsets(rank TVB + l - 1,l),s -> apply(#s, i -> s#i-i));
        allind := sort unique flatten apply(ind, permutations);
        indtable := hashTable apply(#ind, i -> ind#i => i);
        newfM := apply(#R, t -> (
                M := mutableMatrix(ring TVB,#ind,#ind);
                for i in ind do (
                    for j in allind do (
                        M_(indtable#(sort j),indtable#i) = M_(indtable#(sort j),indtable#i) + product apply(#j, k -> ((fM_t)_i)_(j#k,k))
                        );
                    );
                matrix M
                )
            );
        newfJ := apply(#R, t -> (
                apply(ind, j -> sum (fJ_t)_j)
                )
            );
        toricVectorBundle(variety TVB, newfM, newfJ)
        )
    )

-- Helper function for areIsomorphic
linearMapFromMatrices = (A1, A2) -> (
    auxMat := A ->(
        basisIndices := {0};
        currentRank := 1;
        candidateIndices :={};
        candidate := {};
        newRank := 0;
        for i from 1 to numColumns A - 1 do (
            candidateIndices = append(basisIndices, i);
            candidate = A_basisIndices; -- columns selected so far
            candidate = candidate | matrix A_i;
            newRank = rank candidate;
            if newRank > currentRank then (
                basisIndices = candidateIndices;
                currentRank = newRank;
            );
        );
      A_basisIndices
    );
    -- We are guaranteed that the colums chosen will be the same
    M1 := auxMat(A1);
    M2 := auxMat(A2);
    -- Define the unique linear map on the basis
    M1 * inverse M2
    )

ToricVectorBundle == ToricVectorBundle := (T1,T2) -> (areIsomorphic(T1,T2))
areIsomorphic = method()
areIsomorphic (ToricVectorBundle,ToricVectorBundle) := Boolean => (T1,T2) -> (
    --First check that the bundles have same rank, defined over same ring and have same base variety before
    --anything else
    jumps := rsort unique flatten filtrationJumps T1;
    if not ((rank T1 == rank T2) and (variety T1 === variety T2) and (ring T1 === ring T2) and (jumps == rsort unique flatten filtrationJumps T2) ) then return false;
    --Checking if T1 and T2 have already been deemed isomorphic. If not, create entries in a cache
    if not T1.cache.?iso then (
        T1.cache.iso = new MutableHashTable;
        );
    if not T2.cache.?iso then (
        T2.cache.iso = new MutableHashTable;
        );
    --If T1 does have an entry for iso in the cache, we check if any of the maps targets is T2
    --i.e. check if we've already deemed T1 iso T2
    if T1.cache.iso#?T2 then return true;    
    if not T1.cache.iso#?T2 then (
        -- first try the identity map
        f := map(T2,T1, matrix id_((ring T1)^(rank T1)));
        areTVBsIso := ((isWellDefined f) and (isInjective f) and (isSurjective f));
        if not areTVBsIso then (
            -- attempt to find an isomorphism
            n:= rank T1;
            aux1 := flatten apply( jumps, j -> apply(rays T1, rho -> filteredPiece(T1, rho, j) ) );
            aux1 =  flatten apply(toList(1..n), i -> select(aux1, M -> numcols M == i ) );
            aux2 := flatten apply( jumps, j -> apply(rays T2, rho ->filteredPiece(T2, rho, j) ) );
            aux2 =  flatten apply(toList(1..n), i -> select(aux2, M -> numcols M == i ) );
            -- When doing the fold the zero columns are automatically removed    
            M1 := fold((i,j) -> i|j, aux1);
            M2 := fold((i,j) -> i|j, aux2);
            isoMatrix := linearMapFromMatrices(M1,M2);
            -- if isoMatrix === {} then return false;
            f = map(T2,T1,isoMatrix^-1);
            areTVBsIso = ((isWellDefined f) and (isInjective f) and (isSurjective f));
            );
        if areTVBsIso then (
            T1.cache.iso#T2 = f;
            finv := map(T1,T2,(map f)^-1);
            T2.cache.iso#T1 = finv;
            );
        areTVBsIso
        )
    )

isomorphism (ToricVectorBundle,ToricVectorBundle) := Boolean => o -> (T1,T2) -> (
    if not areIsomorphic(T1,T2) then error("The bundles are not isomorphic");
    T1.cache.iso#T2
    )

-- Not sure what to do about caching this method, but we should include it. 
isTwistOf = method()
isTwistOf (ToricVectorBundle, ToricVectorBundle) := (E1, E2) -> (
    if (variety E1) =!= (variety E2) then return false;
    X := variety E1;
    -- For each ray, take the smallest filtered piece of E1 and place it in the position of the
    -- smallest filtered piece of E2. Then check if the resulting bundle is isomorphic to E2.
    (j1,j2) := ((filtrationJumps E1)/min, (filtrationJumps E2)/min);
    D := toricDivisor(j2 - j1, X);
    areIsomorphic(E1 ** lineBundle D, E2)
    )

-------------------------------------------------------------------------------------
-- COHOMOLOGICAL COMPUTATIONS
-------------------------------------------------------------------------------------

-- PURPOSE : Computing the Cech complex of a vector bundle
cechComplex = method()
cechComplex (ZZ,ToricVectorBundle,Matrix) := (k,T,u) -> (
    -- Checking for input errors
    dimvar := dim variety T;
    if numRows u != dimvar or numColumns u != 1 then error("Expected a matrix with 1 column and ", toString dimvar, " rows.");
    if ring u =!= ZZ then error("The degree has to be an integer vector.");
    if k < -1 or dimvar+1 < k then error("k has to be between 0 and the variety dimension for the k-th cohomology");
    -- For a given space F1 at chain k in the filtration together with the degree vector 'u' and the information of the bundle this auxiliary 
    -- function computes the boundary operator to the next chain (k+1) which is F1toF2, the dimensions of the summands of 'F1' in 'F1columns' 
    -- and the next chain 'F2'
    makeNewDiffAndTarget := (F1,u,fMT,rT,bT,tvbR,tvbrank,k,n) -> (
        F2 := {};
        F1toF2 := {};
        counter := 0;
        F1columns := {};
        -- if k==n then the next chain is 0 as well as the boundary operator
        if k == n then (
            F2 = {(0,{},map(tvbR^tvbrank,tvbR^0,0))};
            F1toF2 = {};
            F1columns = {0 => tvbrank})
        -- k==n-1 then the next chain is "complete bundle" and the boundary operator is the map of all summands of Fn-2
        else if k == n-1 then (
            F2 = {(0,{},map(tvbR^tvbrank,tvbR^tvbrank,1))};
            F1toF2 = apply(pairs F1, (j,dat) -> (
                    F1columns = append(F1columns,j => numColumns(dat#1));
                    (j,0,dat#1))))
        else (
            -- for each cone in F1 compute the cones of one dimension less and their bundle
            scan(pairs(F1), (num,dat) -> (
                    R := dat#0;
                    Er := dat#1;
                    -- go through the rays of the cone and remove each of them at a time
                    scan(#R, i -> (
                            Ri := drop(R,{i,i});
                            pos := position(F2, f -> f#1 === Ri);
                            -- Check if the resulting cone already exists in the new chain F2, if so just add Er to the boundary operator
                            if pos =!= null then F1toF2 = append(F1toF2,(num,pos,((-1)^i)*Er)) else (
                                -- if not compute E for new cone and append it to F2
                                Esum := apply(Ri, r -> (rT#r,((transpose u)*r)_(0,0),r));
                                Esum = apply(Esum, e -> (e#0,positions(flatten entries(fMT#(e#2)), j -> (j <= e#1)),e#2));
                                if any(Esum, e -> e#1 == {}) then F2 = append(F2,(counter,Ri,map(tvbR^tvbrank,tvbR^0,0))) else (
                                    E := map(tvbR^tvbrank,tvbR^tvbrank,1);
                                    Esum = select(Esum, e -> sort(e#1) != toList(0..tvbrank-1));
                                    Esum = apply(Esum, e -> (bT#(e#2))_(e#1));
                                    scan(Esum, A -> E = intersectMatrices(E,A));
                                    F2 = append(F2,(counter,Ri,E)));
                                F1toF2 = append(F1toF2,(num,counter,((-1)^i)*Er));
                                counter = counter + 1)));
                    -- Save the dimension of Er into F1columns
                    F1columns = append(F1columns,num => numColumns Er))));
        (hashTable apply(F1toF2, f -> (f#0,f#1) => f#2),hashTable F1columns,hashTable apply(F2, f -> f#0 => (f#1,f#2))));
    if not T.cache.?cech then T.cache.cech = new MutableHashTable;
    raysT := rays T;
    fMT := hashTable apply(raysT, rho -> transpose matrix {rho} => matrix {-(details T)#rho_1} );
    tvbR := ring T;
    tvbrank := rank T;
    n := dimvar;
    -- if k==n+1 the chain is 0 and there is no map
    if k == n+1 then (hashTable {0 => ({},map(tvbR^tvbrank,tvbR^0,0))},hashTable {},hashTable {}) else (
        rT :=  hashTable apply(#raysT, i -> transpose matrix {raysT_i} => i );
        bT :=  hashTable apply(raysT, rho -> transpose matrix {rho} => (details T)#rho_0 );
        if not T.cache.cech#?(k,u) then (
            -- rT will be used to sort the rays
    
            -- if the previous chain has not been computed we have to compute the cones of the right dimension (n-k)
            if not T.cache.cech#?(k-1,u) or k == 0 then (
                -- if k==n then the chain is the "complete bundle" and the next chain is 0
                if k == n then (
                    T.cache.cech#(k,u) = (hashTable {0 => ({},map(tvbR^tvbrank,tvbR^tvbrank,1))},hashTable {0 => tvbrank},hashTable {});
                    T.cache.cech#(k+1,u) = hashTable {0 => ({},map(tvbR^tvbrank,tvbR^0,0))})
                -- if k==-1 the chain is 0
                else if k == -1 then T.cache.cech#(k,u) = (hashTable { 0 => ({},map(tvbR^tvbrank,tvbR^0,0))},hashTable {0 => 0},hashTable {})
                else (
                    F1 := faces(k,fan T);
                    Frays := rays fan T;
                    Flineality := linealitySpace fan T;
                    F1 = apply(F1, f-> posHull(Frays_f, Flineality));
                    -- for each n-k cone in the fan compute Er, the bundle over this cone for the degree u
                    F1 = hashTable apply(#F1, Cnum -> (
                            C := F1#Cnum;
                            R := (rays C);
                            R = apply(numColumns R, i -> (R_{i}));
                            R = sort apply(R, r -> (rT#r,r));
                            Esum := apply(R, r -> (r#0,((transpose u)*(r#1))_(0,0),r#1));
                            R = apply(R, r -> (r#1));
                            Esum = apply(Esum, e -> (e#0,positions(flatten entries fMT#(e#2), j -> (j <= e#1)),e#2));
                            if any(Esum, e -> e#1 == {}) then Cnum => (R,map(tvbR^tvbrank,tvbR^0,0)) else (
                                E := map(tvbR^tvbrank,tvbR^tvbrank,1);
                                Esum = select(Esum, e -> sort(e#1) != toList(0..tvbrank-1));
                                Esum = apply(Esum, e -> (bT#(e#2))_(e#1));
                                scan(Esum, A -> E = intersectMatrices(E,A));
                                Cnum => (R,E))));
                    -- Compute the boundary operator with the auxiliary function
                    (F1toF2,F1columns,F2) := makeNewDiffAndTarget(F1,u,fMT,rT,bT,tvbR,tvbrank,k,n);
                    T.cache.cech#(k,u) = (F1,F1columns,F1toF2);
                    -- Save the next chain to the cache
                    if not T.cache.cech#?(k+1,u) then T.cache.cech#(k+1,u) = F2))
            else (
                -- if the previous chain exists use this to compute the chain in question
                F10 := T.cache.cech#(k-1,u);
                (F10toF11,F10columns,F11) := makeNewDiffAndTarget(F10,u,fMT,rT,bT,tvbR,tvbrank,k-1,n);
                (F11toF12,F11columns,F12) := makeNewDiffAndTarget(F11,u,fMT,rT,bT,tvbR,tvbrank,k,n);
                T.cache.cech#(k-1,u) = (F10,F10columns,F10toF11);
                T.cache.cech#(k,u) = (F11,F11columns,F11toF12);
                -- save the next chain to the cache as well
                if not T.cache.cech#?(k+1,u) then T.cache.cech#(k+1,u) = F12))
        -- if the cache only consists of the chain but not of the boundary operator compute this
        else if not instance(T.cache.cech#(k,u),Sequence) then (
            F21 := T.cache.cech#(k,u);
            (F21toF22,F21columns,F22) := makeNewDiffAndTarget(F21,u,fMT,rT,bT,tvbR,tvbrank,k,n);
            T.cache.cech#(k,u) = (F21,F21columns,F21toF22);
            if not T.cache.cech#?(k+1,u) then T.cache.cech#(k+1,u) = F22);
        T.cache.cech#(k,u)))

-- PURPOSE : Computing the cohomology of a given ToricVectorBundle
cohom = method()
cohom (ZZ,ToricVectorBundle,Matrix) := (k,T,u) -> (
    if not T.cache.?HH then T.cache.HH = new MutableHashTable;
    if not T.cache.HH#?(k,u) then (
        -- Get the k-1 th, k th and k+1 th chain in the Cech complex
        (F1,F1columns,F1toF2) := cechComplex(k-1,T,u);
        (F2,F2columns,F2toF3) := cechComplex(k,T,u);
        F3 := (cechComplex(k+1,T,u))#0;
        tvbR := ring T;
        tvbrank := rank T;
        -- Generate the two boundary operators
        MapF1toF2 := matrix apply(#F2, j -> apply(#F1, i -> if F1toF2#?(i,j) then F1toF2#(i,j) else map(tvbR^tvbrank,tvbR^(F1columns#i),0)));
        MapF2toF3 := matrix apply(#F3, j -> apply(#F2, i -> if F2toF3#?(i,j) then F2toF3#(i,j) else map(tvbR^tvbrank,tvbR^(F2columns#i),0)));
        -- Compute the cohomology
        d := (rank ker MapF2toF3)-(rank image MapF1toF2);
        T.cache.HH#(k,u) = (grRing T)^(toList(d:flatten entries(-u))));
    T.cache.HH#(k,u)
    )

eulerChi = method()
eulerChi (Matrix,ToricVectorBundle) := (u,T) -> (
    if not T.cache.?eulerChi then T.cache.eulerChi = new MutableHashTable;
    if not T.cache.eulerChi#?u then (
        n := dim variety T;
        -- Compute the Cech complex and compute the alternating sum of the dimensions
        T.cache.eulerChi#u = sum apply(n+1, i -> (-1)^i * sum values (cechComplex(i,T,u))#1););
        T.cache.eulerChi#u
    )

eulerChi ToricVectorBundle := T -> ( 
    -- Compute the set of degrees with possible cohomology
    L := latticePoints deltaE T;
    -- Sum up their characteristics
    sum apply(L, l -> eulerChi(l,T))
    )

cohomology(ZZ,ToricVectorBundle,Matrix) := opts -> (i,T,weight) -> cohom(i,T,weight)
cohomology(ZZ,ToricVectorBundle,List) := opts -> (i,T,P)-> (
    if opts.Degree == 1 then print ("Number of degrees to calculate: "|(toString(#P)));
    for j in P list (
        if opts.Degree == 1 then << "." << flush;
        j = cohomology(i,T,j);
        if j != 0 then j else continue)
    )
cohomology(ZZ,ToricVectorBundle) := opts -> (i,T)-> (
    L := cohomology(i,T,latticePoints deltaE T,Degree => opts.Degree);
    if L == {} then (grRing T)^0 else directSum L
    )

hh(ZZ,ToricVectorBundle) := ZZ => (i,T) -> rank cohomology(i,T)
deltaE = method()
deltaE ToricVectorBundle := (cacheValue symbol deltaE)( tvb -> (
        if not isComplete variety tvb then error("The toric variety needs to be complete.");
        n := dim variety tvb;
        -- Extracting necessary data with rays as column matrices to use old code
        rayTable := apply( rays tvb, s -> transpose matrix {s});
        l := #rayTable;
        -- The sign change is to use the previous code
        j:={};
        fMT := hashTable apply(rayTable, i -> (j = -(details tvb)#(flatten entries i)_1; i => matrix{{-(min j),max j}}));
        sset1 := select(subsets(rayTable,n), s -> rank matrix {s} == n);
        convexHull matrix {apply(sset1, s -> (
                    M := transpose matrix {apply(s, r -> (-r | r) || (fMT#r))};
                    vertices polyhedronFromHData(M_{0..n-1},M_{n})))}
        )
    )

isGeneral = method()
isGeneral ToricVectorBundle :=  E -> (
    if E.cache.?isGeneral then( return E.cache.isGeneral);
    -- list the max cones
    MCones:= max variety E;
    raysX := rays E;
    r := rank E;
    R := ring E;
    fJumps := filtrationJumps E;
    E.cache.isGeneral = true;
    -- Get a list for each ray of the posible filtered pieces
    allPieces := apply(#raysX, p -> apply( unique (fJumps_p), i -> image filteredPiece(E, raysX_p, i) ) );
    -- For a maximal cone, we perform a recursive check: 
    -- the input is a list of as many list as rays the cone had of vector spaces that we have to compare
    recursiveCheck := (L,Es) ->(
        if L =!= {} then (apply(L_0, vs -> recursiveCheck(drop(L,1), Es|{vs}) ))
        else(
            -- at this point we have L empty and Es the list of vector spaces to compare
            minCodim:= min(r, sum apply( Es, vs -> r - rank vs));
            Eint := image id_(R^r);
            scan(Es, A -> Eint = intersect(Eint,A));
            dimInt:= r - rank Eint;
            if minCodim != dimInt then( E.cache.isGeneral = false; return E.cache.isGeneral );    
            );
        );
    -- We apply the check to all the cones
    apply( MCones, sigm -> recursiveCheck(allPieces_sigm ,{}) );
    E.cache.isGeneral
    )


-- PURPOSE : Computing the Cartier index of a Weil divisor
--   INPUT : '(L,F)',  where 'F' is a Fan and 'L' is a list of integers defining a Weil divisor
--  OUTPUT : The smallest multiple of the divisor which is Cartier if the divisor is QQ-Cartier, if not 
--     	     an error is returned
cartierIndex = method(TypicalValue => ZZ)

cartierIndex (NormalToricVariety, List) := (X, L) ->(
    -- TODO : add checks for the Cartier index to make sense    
    if any(L, l -> not instance(l,ZZ)) then error("The weights have to be in ZZ.");
    denom := 1; 
    raysX := rays X;
    maxCs := X.max;
    Frays := transpose  matrix raysX;
    L = hashTable apply(#raysX, i -> Frays_i => L_i);
    n:= ambDim ( fan X);
    scan(maxCs, C -> (
	       rC := Frays_C;
	       -- Taking the first n x n submatrix
	       rC1 := rC_{0..n-1};
	       -- Setting up the solution vector by composing the corresponding weights
	       v := matrix apply(n, i -> (c := entries rC1_{i}; {-(L#c)}));
	       -- Computing the degree vector
	       w := vertices polyhedronFromHData(matrix {toList(n:0)},matrix {{0}},transpose rC1,v);
	       -- Checking if w also fulfils the equations given by the remaining rays
	       if numColumns rC != n then (
		    v = v || matrix apply(toList(n..(numColumns rC)-1), i -> {-(L#(entries rC_{i}))});
	            if (transpose rC)*w - v != 0 then error("The weights do not define a Cartier divisor."));
	       -- Check if w is QQ-Cartier
	       scan(flatten entries w, e -> denom = lcm(denominator e ,denom))));
     denom
     )




cartierIndex (List,Fan) := (L,F) -> (
     rl := raySortOfFan F;
     -- Checking for input errors
     if #L != #rl then error("The number of weights has to equal the number of rays.");
     n := ambDim F;
     -- Checking for further errors and assigning the weights to the rays
     L = hashTable apply(#rl, i -> (if class L#i =!= ZZ then error("The weights have to be in ZZ."); rl#i => L#i));
     -- Keeping track of the lowest common multiple of denominators of the degrees,
     -- to check whether the divisor itself is Cartier or which multiple
     denom := 1;
     -- Computing the degree vector for every top dimensional cone
     Frays := rays F;
     scan(sort maxCones F, C -> (
	       rC := Frays_C;
	       -- Taking the first n x n submatrix
	       rC1 := rC_{0..n-1};
	       -- Setting up the solution vector by composing the corresponding weights
	       v := matrix apply(n, i -> (c := rC1_{i}; {-(L#c)}));
	       -- Computing the degree vector
	       w := vertices polyhedronFromHData(matrix {toList(n:0)},matrix {{0}},transpose rC1,v);
	       -- Checking if w also fulfils the equations given by the remaining rays
	       if numColumns rC != n then (
		    v = v || matrix apply(toList(n..(numColumns rC)-1), i -> {-(L#(rC_{i}))});
	            if (transpose rC)*w - v != 0 then error("The weights do not define a Cartier divisor."));
	       -- Check if w is QQ-Cartier
	       scan(flatten entries w, e -> denom = lcm(denominator e ,denom))));
     denom)

randomDeformation = method()
randomDeformation ( ToricVectorBundle ) :=(tvb) ->(
    k := rank tvb;    
    R:= ring tvb;
    -- Change the matrices in the filtration and preserve the jumps
    newMatrices := apply(filtrationMatrices tvb, M ->(
            -- TODO How do we want to get the random matrices?
            A := random(R^k, R^k);
            while det A == 0 do (A = random(R^k, R^k));
            A)
        );
    toricVectorBundle(variety tvb, newMatrices, filtrationJumps tvb)
    )

tensor(ToricVectorBundle, ToricVectorBundle) := ToricVectorBundle => {} >> opts -> (tvb1, tvb2) -> (
    if variety(tvb1) =!= variety(tvb2) then(error("Expected the bundles to be over the same toric variety.") );
    X:=variety(tvb1 );
    nrays := # rays (variety(tvb1 ));
    L1:= filtrationMatrices( tvb1 ); 
    L2:= filtrationMatrices (tvb2 );
    Lnew:= apply(nrays, i -> L1_i**L2_i );
    J1:= filtrationJumps( tvb1 ); 
    J2:= filtrationJumps (tvb2 );
    -- TODO check that this is what we want
    Jnew := apply(nrays, p -> flatten apply(J1_p, e1 -> flatten apply(J2_p, e2 -> e1 + e2)));
    toricVectorBundle(X, Lnew, Jnew)
    )
ToricVectorBundle ** ToricVectorBundle := (tvb1,tvb2) -> tensor(tvb1,tvb2)

twist = method()
twist(ToricVectorBundle, ToricDivisor) := (E, D) -> E ** lineBundle D
twist(ToricVectorBundle, List) := (E, s) -> E ** lineBundle(variety E, s)

--------------------------------------
-- MAPS
--------------------------------------

ToricVectorBundleMap = new Type of HashTable
ToricVectorBundleMap.synonym = "map of toric vector bundles on a fixed toric variety"
source ToricVectorBundleMap := ToricVectorBundle => f -> f.source
target ToricVectorBundleMap := ToricVectorBundle => f -> f.target
map ToricVectorBundleMap := Matrix => opts -> f -> f.map
matrix ToricVectorBundleMap := Matrix => f -> f.map

net ToricVectorBundleMap := f -> (
    arrow := " <--";
    for i to width net map f do arrow = arrow | "-";
    themap := (arrow | "-- ") || ("    " | net map f);
    "ToricVectorBundleMap " || (net expression target f | themap | net expression source f)
    )

-- We allow defining a map that is not well defined
map(ToricVectorBundle, ToricVectorBundle, Matrix):= ToricVectorBundleMap => opts -> (E2, E1, M) ->(

    -- if numRows M =!= rank E2 or numColumns M =!= rank E1 then error " The dimensions of the matrix don't match the ranks of the bundles";
    if ring M =!= ring E1 or ring M =!= ring E2 then error " The matrix needs to be defined over the same ring as the bundles";
    if variety E1 =!= variety E2 then error "The base varieties of the bundles have to coincide";
    new ToricVectorBundleMap from{
        symbol source => E1,
        symbol target => E2,
        symbol map => M,
        symbol cache => new CacheTable
    }
)

ToricVectorBundleMap#id = E -> map(E,E, id_(ring E^(rank E) ))

isWellDefined ToricVectorBundleMap := Boolean => f ->(
    if f.cache.?isWellDefined then return f.cache.isWellDefined;
    K := keys f;
    expectedKeys := set{symbol source, symbol target, symbol map, symbol cache};
    if set K =!= expectedKeys then (
        if debugLevel > 0 then (
            added := toList(K - expectedKeys);
            missing := toList(expectedKeys - K);
            if #added > 0 then 
            << "-- unexpected key(s): " << toString added << endl;
            if #missing > 0 then 
            << "-- missing keys(s): " << toString missing << endl
            );
        return false
        );
    --Check types
    if not instance(f.source, ToricVectorBundle) then (
        if debugLevel > 0 then (
            << "-- expected the source to be a ToricVectorBundle" << endl
            );
        return false
        );
    if not instance(f.target, ToricVectorBundle) then (
        if debugLevel > 0 then (
            << "-- expected the target to be a ToricVectorBundle" << endl
            );
        return false
        );
    if not instance(f.map, Matrix) then (
        if debugLevel > 0 then (
            << "-- expected the map to be a Matrix" << endl
            );
        return false
        );
    if not instance(f.cache, CacheTable) then (
        if debugLevel > 0 then (
            << "-- expected cache to be a CacheTable" << endl
            );
        return false
        );    
    --Check mathematical structure
    E1 := source f;
    E2 := target f;
    M := f.map;
    RX := ring E1;
    Xrays := rays variety E1;
    r := rank E1;
    for p in Xrays do (
        j := flatten join(filtrationJumps source f, filtrationJumps target f);
        -- The next condition is only for the isomorphism between trivial bundles of rank 0
        if j == {} then(f.cache.isWellDefined = true;
                return f.cache.isWellDefined);
        m1 := min j;
        m2 := max j;
        amb := module (ring E2) ^ (rank (filtrationMatrices E2)_0);
        for i from m1 to m2 do (
            -- not writing rank E2 allows for matrices that are not square (see cokernel)
            f1 := map(amb, , sub( M* filteredPiece(E1,p,i), RX));
            f2 := map(amb, , sub(filteredPiece(E2,p,i),RX));
            
            if not isSubset(image f1, image f2) then (
                if debugLevel > 0 then (
                    << ("--the image of the source is not contained in the target at index " | net i) << endl
                    );
                f.cache.isWellDefined = false;
                return f.cache.isWellDefined
                );
            );
        );
    f.cache.isWellDefined = true;
    return f.cache.isWellDefined
    )

isInjective (ToricVectorBundleMap) := f -> (
    if not isWellDefined f then (
        if debugLevel > 0 then (
            << "-- the map is not well defined" << endl
            );
        return false
        );
    if not isInjective (map f) then (
        if debugLevel > 0 then (
            << "-- the map is not injective" << endl);
        return false
        );
    X := variety(source f);
    for p in rays X do (
        r := flatten join(filtrationJumps source f, filtrationJumps target f);
        if r == {} then(return true);
        m1 := min r;
        m2 := max r;
        for i from m1 to m2 do (
            if not (numColumns filteredPiece(source f, p, i) <= numColumns filteredPiece(target f, p, i)) then (
                if debugLevel > 0 then (
                    << "some error message" << endl
                    );
                return false
                );
            );
        );
    true
    )

isSurjective (ToricVectorBundleMap) := f -> (
    if not isWellDefined f then (
        if debugLevel > 0 then (
            << "-- the map is not well defined" << endl);
        return false
        );
    if not isSurjective (map f) then (
        if debugLevel > 0 then (
            << "-- the map is not surjective" << endl);
        return false
        );
    X := variety(source f);
    for p in rays X do (
        r := flatten join(filtrationJumps source f, filtrationJumps target f);
        if r == {} then(return true);
        m1 := min r;
        m2 := max r;
        for i from m1 to m2 do (
            if not (numColumns filteredPiece(source f, p, i) >= numColumns filteredPiece(target f, p, i)) then (
                if debugLevel > 0 then (
                    << "some error message" << endl
                    );
                return false
                );
            );
        );
    return true
    )


-- Auxiliary fucntion for computing the jumps that happened in a list of matrices in a filtration
-- Takes a matrix to which we want to assing the jums, a list of the filtered pieces and the minimun idex where it stats
jumpsAux = (basemat, L,mm) ->(
    ref := transpose entries basemat;
    r:= # ref;
    -- Extracts the positions where the vectors appear in the original matrix
    Jl := apply(#L, i->(positions(ref, v -> isSubset({v}, transpose entries (L_i)))));
    apply(sum(#Jl,  i ->apply(#ref, j -> if member(j, Jl_i) then 1 else 0)), n -> n+mm-1)    
)
-- Auxiliary function to simplify the choice of basis done
-- Given a non square matrix of full rank and a list of jumps it returns a square matrix and a list of jumps
-- such that the filtration defined is the same as the one we started with. 
-- This fucntion is used in weilToKyachko but also in coker, image and ker
-- TODO: check that it interacts correctly with isWellDefined ToricVectorBundle
-- The input is of the form ML={Matrix, List}
adaptedBasis = (ML) -> (
    M:= ML_0;
    L:= ML_1;
    rk := rank M;
    if rk== numColumns M then( return {M,L});
    levels := reverse sort unique L;
    cols := {};
    jumps := {};
    B := M_{};
    for a from 0 to #levels-1 do (
        inds := positions(L, i -> i == levels_a);
        for i from 0 to #inds-1 do (
            C := M_(cols |{inds_i});
            if rank C > rank B then (
                cols = append(cols,inds_i);
                jumps = append(jumps,levels_a);
                B = C;
                if rank C == rk then( break);
            );
        );
    );
    {M_cols, jumps}
)

-- TODO NEEDS TO BE FIXED

image (ToricVectorBundleMap) := f ->(
    if isSurjective(f) then( return target f ); 
    if not isWellDefined(f) then ( error (" The map is not well defined"));
    M := f.map;
    E1:= source f;
    X:= variety E1;
    Xrays := rays E1;
    minj:= min flatten filtrationJumps(E1);
    maxj:= max flatten filtrationJumps(E1);
    steps:=  toList(minj..maxj);
    -- get the images of the filtered pieces
    L := apply(Xrays,  p ->
        apply(steps, i ->(
                prod := M * filteredPiece(E1,p,i);
                -- take the image of the filtered piece and prune it.
                pr := (prune image prod).cache.pruningMap;
                -- then apply that pruning map.
                prod * matrix pr
                ))
        );
    -- Define the new data
    newMatrices:= apply(L, i ->  matrix fold ( (A,B)-> A|B, i) );
    newJumps := apply( # Xrays , i -> jumpsAux(newMatrices_i, L_i, minj ) );
    newData := {newMatrices, newJumps};
    -- Refine it it needed
    if numcols newMatrices_0 =!= numrows newMatrices_0 then(
    newData = transpose apply( transpose  newData, a -> adaptedBasis(a) ););
    newMatrices = newData_0;
    -- if the map is not surjective, then we also need to make sure that the
    -- matrices are square, which we do one final prune for.
    newMatrices = for m in newMatrices list (
        if numcols m != numrows m then (
            pr := (prune image transpose m).cache.pruningMap;
            transpose (transpose m * matrix pr)
            )
        else m
        );
    newJumps= newData_1;
    toricVectorBundle(X, newMatrices, newJumps)
)

-- TODO fix jumps

kernel (ToricVectorBundleMap) := opts -> f ->(
    E1:= source f;
    X:= variety E1;
    if isInjective(f) then( return trivialBundle(X,0) ); 
    if not isWellDefined(f) then ( error (" The map is not well defined"));
    M := f.map;
    Xrays := rays E1;
    minj:= min flatten filtrationJumps(E1);
    maxj:= max flatten filtrationJumps(E1);
    steps:=  toList(minj..maxj);
    kerM := kernel M;
    amb:= target gens kerM;
    pr:= (prune kernel (M)).cache.pruningMap;
    ipr := map(source pr, target pr, inverse pr);
    -- Get the kernel of the pieces
    L:= apply(Xrays,  p ->
        apply(steps, i ->(
            ipr*inducedMap(kerM,intersect(image map(amb, , filteredPiece(E1,p,i)), kerM))
        ))
    );
    -- Define the new data
    -- The command matrix is there so that the map is simplify to be betweent free modules
    newMatrices:= apply(L, i ->  matrix fold ( (A,B)-> A|B, i) );
    newJumps := apply( # Xrays , i -> jumpsAux (newMatrices_i, L_i, minj ) );
    newData := transpose {newMatrices, newJumps};
    -- Refine it it needed
    newData = transpose apply( newData, a -> adaptedBasis(a) );
    newMatrices = newData_0;
    newJumps= newData_1;
    toricVectorBundle(X, newMatrices, newJumps)
)




cokernel (ToricVectorBundleMap) := f ->(
    if not isWellDefined(f) then ( error (" The map is not well defined"));
    if isSurjective(f) then( return trivialBundle(variety source (f), 0) ); 
    
    M := f.map;
    E1:= source f;
    E2 := target f;
    X:= variety E1;
    RX:= ring E1;
    Xrays := rays E1;
    minj:= min flatten join(filtrationJumps(E1), filtrationJumps(E2));
    maxj:= max flatten join(filtrationJumps(E1), filtrationJumps(E2));
    steps:=  toList(minj..maxj);
    cokerM := cokernel M;
    pr:= (prune cokerM).cache.pruningMap;
    ipr := map(source pr, target pr, inverse pr);
    L:= apply(Xrays,  p ->
        apply(steps, i ->(
                -- TO DO: fix this
                -- This will give the data for the cokerenel but where the ambien matrix need not be square
                -- We later need to get an square matrix out of it by "selecting a subset of the columns" (using adaptedBasis) or using some other method 
                -- The choices made here (and below) interact with how isIsomorphic works etc
                amb := module (ring E2) ^ (rank E2);
                f1 := image map(amb, , sub(M * filteredPiece(E1,p,i),RX));
                f2 := image map(amb, , sub(filteredPiece(E2,p,i),RX));
                ipr*inducedMap(cokerM, f2/f1 ) 

                ))
        );
    -- Define the new data
    newMatrices:= apply(L, i ->  matrix fold ( (A,B)-> A|B, i) );
    newJumps := apply( # Xrays , i -> jumpsAux(newMatrices_i, L_i, minj ) );
    (newMatrices, newJumps)= toSequence transpose apply(transpose{newMatrices, newJumps}, D -> adaptedBasis D );
    toricVectorBundle( X, newMatrices, newJumps)
)

ToricVectorBundleMap ++ ToricVectorBundleMap := (tvbmap1,tvbmap2) -> (
    map(tvbmap1.target ++ tvbmap2.target, tvbmap1.source ++ tvbmap2.source, tvbmap1.map ++ tvbmap2.map)
)

ToricVectorBundleMap ** ToricVectorBundleMap := (tvbmap1,tvbmap2) -> (
    map(tvbmap1.target ** tvbmap2.target, tvbmap1.source ** tvbmap2.source, tvbmap1.map ** tvbmap2.map)
)

 ---------------------------------------
-- WEIL DECORATIONS
---------------------------------------

-- Torus-invariant Weil divisors are compared componentwise.  This is a partial
-- order, so incomparable pairs are reported as such.
ToricDivisor ? ToricDivisor := (D1, D2) -> (
    a := entries vector D1;
    b := entries vector D2;
    if a === b then symbol ==
    else if all(a, b, (i, j) -> i <= j) then symbol <
    else if all(a, b, (i, j) -> i >= j) then symbol >
    else symbol incomparable)

-- Meet and join for that order.  The join is what cuts out an intersection of
-- two stratum closures: E_{>= D1} * E_{>= D2} = E_{>= D1 v D2}.
gcd(ToricDivisor, ToricDivisor) := ToricDivisor => (D1, D2) -> toricDivisor(
    apply(entries vector D1, entries vector D2, min), variety D1)
lcm(ToricDivisor, ToricDivisor) := ToricDivisor => (D1, D2) -> toricDivisor(
    apply(entries vector D1, entries vector D2, max), variety D1)

-- A Weil decoration of a toric vector bundle, in the sense of Altmann,
-- Hochenegger and Witt: the map sending a vector of the fiber over the identity
-- to the largest torus-invariant Weil divisor D with e in E_{>= D}.  Since the
-- map is constant on strata, it is recorded by its strata: each stratum closure,
-- which is a subspace of the fiber, paired with the divisor decorating it.  The
-- zero subspace is decorated by infinity.
WeilDecoration = new Type of HashTable
WeilDecoration.synonym = "Weil decoration"
globalAssignment WeilDecoration

net WeilDecoration := WD -> (
    "Weil decoration of rank " | toString WD.rank |
    " with " | toString(#WD.strata) | " nonzero strata")

variety WeilDecoration := WD -> WD.variety
rank WeilDecoration := ZZ => WD -> WD.rank

-- The stratum closures with their divisors, sorted by dimension.
strata = method()
strata WeilDecoration := List => WD -> WD.strata

-- NOTE: The trivial strata is excluded for convenience in coding.
weilDecoration = method()
weilDecoration ToricVectorBundle := WeilDecoration => V -> (
    X := variety V;
    A := rays X;
    L := flatten filtrationJumps V;
    n := length A;
    minInds := toList(n : min L);
    maxInds := toList(n : max L);
    -- For each subspace arising as an intersection of filtered pieces, record the
    -- componentwise *largest* index vector producing it, since the decoration of
    -- a vector is the largest D with e in E_{>= D}.  If two index vectors produce
    -- the same intersection then so does their componentwise maximum, so that
    -- maximum is also the lexicographic maximum; traversing the box in
    -- lexicographic order and overwriting therefore leaves it behind.
    strataIntersections := new MutableHashTable;
    for inds in minInds .. maxInds do (
	-- the filtered piece on each ray at the given index
	pieces := apply(A, inds, (rho, j) -> image filteredPiece(V, rho, j));
	W := intersect pieces;
	-- a vanishing intersection is not a stratum for us.
	if rank W > 0 then strataIntersections#W = toList inds);
    -- Sort the strata by dimension, breaking ties by the index vector.  Note that
    -- the Matroids package globally redefines sort(List, Function) with a
    -- deepSplice that flattens any sequences in the list, so a list of pairs must
    -- not be sorted that way; sorting an auxiliary list of triples is safe.
    ks := keys strataIntersections;
    S := apply(sort apply(#ks, i -> (rank ks#i, strataIntersections#(ks#i), i)),
	t -> (ks#(last t), strataIntersections#(ks#(last t))));
    new WeilDecoration from {
	symbol variety => X,
	symbol strata  => apply(S, (W, inds) -> (W, toricDivisor(inds, X))),
	symbol rank    => rank V,
	symbol cache   => new CacheTable})

weilToKlyachko = method()
weilToKlyachko WeilDecoration := ToricVectorBundle => WD ->
    weilToKlyachko(variety WD, WD)

weilToKlyachko(NormalToricVariety, WeilDecoration) := ToricVectorBundle => (X, WD) ->
    weilToKlyachko(X, apply(strata WD, (W, D) -> (W, entries vector D)))

weilToKlyachko(NormalToricVariety, List) := (X, WD) ->(
    -- The input is a list of pairs (stratum closure, list of divisor coefficients).
    -- create a matrix with jumps for each ray that will later be refined
    Maux := matrix transpose flatten apply(WD, (V, inds) -> entries \ V_*);
    Jaux := apply(#rays X, j -> { Maux, flatten apply(WD, (V, inds) -> toList(numgens V : inds_j)) });
    -- Simplify the data to get square matrices
    data := transpose apply(Jaux, adaptedBasis);
    toricVectorBundle(X, data_0, data_1))

-- Input: weilDecoration for a ToricVectorBundle
-- Output: the (not necessarily saturated!) chains in the poset of strata
posetChains := (WD,n) -> (
    sWD := strata WD;
    if n < 0 then return error("need nonnegative n");
    if n == 0 then return apply(sWD, l -> {{numgens l_0, l_1}});
    divs := flatten posetChains(WD,0);
    prevChains := posetChains(WD,n-1);
    flatten for c in prevChains list (
        currdiv := first c;
        for newdiv in divs list (
            if currdiv_0 >= newdiv_0 then continue
            else
            if currdiv_1 < newdiv_1 then continue
            else {newdiv} | c
            )
        )
    )
posetChains = memoize posetChains

firstChernClass = method()
firstChernClass ToricVectorBundle := E -> (
    D := weilDecoration E;
    r := rank E;
    sum flatten for i to r-1 list (
        ichains := posetChains(D,i);
        for c in ichains list (-1)^i * (last c)_0 * (first c)_1
        )
    )

--------------------------------------------------------------
-- GETTER FUNCTIONS FOR WEIL DECORATIONS
--------------------------------------------------------------
--not sure what other getter functions we would want, just one to recover the torus-invariant divisors
--for now

--do we want WEILDECORATION to be a type, or keep it as a list?

--for now, this simply gives the list of divisors as a list of ordered coefficients
--I would like to implement it so that they return as a list of ToricDivisors if that
--would make sense? So we need to associate our Weil Decoration to the appropriate NormalToricVariety?
weilDecorationDivisors = method()
weilDecorationDivisors List := weilDecorationList -> (
    divList := {};
    --assumes first entry in weilDecorationList is {0,infinity}
    for i from 1 to #weilDecorationList - 1 do (
        divList = append(divList, weilDecorationList#i#1)
        );
    divList
    )



---------------------------------------
-- COX MODULES CONVERSION
---------------------------------------

-- Given a fine graded module over the Cox ring of a toric variety we obtain an equivariant sheaf.

-- The code that follows take a module, assuming that it defines a toric vector bundle and returns its Klyachko description. 


--Auxiliary fucntion for moduleToKlyachko

fineGr = (S,A,n) -> (
-- TODO: This correction should be the twist that we are introuducing when assuming MS#0 is {0,...,0}, but it is not working
   -- correction := flatten entries ( matrix(rays X) *( transpose matrix{(degrees source A)_0}));
  -- Source degrees
  p := numColumns (A);
  MS := new MutableHashTable from apply(p , j -> {j,{}});
  -- target degrees
  q := numRows (A);
  NS := new MutableHashTable from apply(q , i -> {i,{}});
  aux := apply(entries A, i -> apply( i, j -> exponents j));
  jnew := 0;
  inew := 0; 
 MS#0 = toList(n:0); 
-- Track lists of degrees instead of cloning the MutableHashTables
  oldMS := apply(p, j -> MS#j);
  oldNS := apply(q, i -> NS#i);
  currentMS :={};
  currentNS :={};

  while isMember({}, values MS) or isMember({}, values NS) do(
      if oldMS == currentMS and oldNS == currentNS then(
          jnew = min apply(p, j -> if MS#j == {} then( j)else( infinity) );
          if jnew != infinity then( MS#jnew= toList(n:0); )else(
          inew = min apply(q, i -> if NS#i == {} then( i)else( infinity) );
          if inew != infinity then( NS#inew= toList(n:0); );
          );
          
      );

      oldMS = apply(p, j -> MS#j);
      oldNS = apply(q, i -> NS#i);

      for j from 0 to p-1 do(
          for i from 0 to q-1 do(
              if (aux_i)_j != {} then(
                  if NS#i !={} and MS#j == {}  then(MS#j = flatten (aux_i)_j + NS#i );
                  if MS#j !={} and NS#i == {} then(NS#i = - flatten (aux_i)_j + MS#j);
              );
          );
      );
      
      currentMS = apply(p, j -> MS#j);
      currentNS = apply(q, i -> NS#i);

  ); 
  sdegs := - apply(p , j -> MS#j );
  tdegs := - apply(q , i -> NS#i );
  R := newRing( S, Degrees => entries id_(ZZ^(n)));
  Anew := map(R^tdegs,R^sdegs,sub(A, R) );
  

)






moduleToKlyachko = method(Options => {Strategy => "image"})
-- A: presentation of the module we are sheafifying that is fine-graded

moduleToKlyachko (NormalToricVariety, Matrix):= opts -> (X,A) -> (
    -- Obtain the ToricVectorBundleMap associated to the presentation
  S := ring A;
  n := numgens S;
  if  all( flatten entries A , p -> # terms p <= 1) != true then( error("The presentation matrix is not equivariant"););

  if not( isHomogeneous A and degrees ring A == entries id_(ZZ^(n)) )then(
    if ring A === ring X then(
    A = fineGr (S,A,n);)else (error("The module is not defined over the Cox ring of the toric variety"););
    S = newRing( S, Degrees => entries id_(ZZ^(n)));
  );
    s0:= trivialBundle(X,0) ;
    sdegs2:= degrees source A;
    tdegs2 := degrees target A;
    sour2 := fold(directSum,s0,  apply(sdegs2, l -> (if l != splice{n:0} then( lineBundle(X, -l ))else(trivialBundle (X,1)) )) );
    t0:= trivialBundle( X,0);
    targ2 := fold(directSum,s0,  apply(tdegs2, l -> (if l != splice{n:0} then( lineBundle(X, -l ))else(trivialBundle (X,1)) )) );
    -- The map evaluates the variables to be 1 which should give the map at the fiber over the identity point
    phi := map( coefficientRing S, S, toList(n:1));
    -- Avoids problems with the image of the map being a module for instance
    Anew :=   matrix entries A; 
    f:= map( targ2 , sour2, phi**Anew);
    f
)



-- M = image matrix...
moduleToKlyachko (NormalToricVariety, Module):= opts -> (X,M) -> (
 M = presentation M;
 return coker moduleToKlyachko(X, M);
)
-- The code that follows take a toric vector bundle with Klyachko description and returns a module over the Cox ring of the toric variety, M, such that the sheafification of M is the starting vector bundle.
-- Note that different modules can have the same associated sheaf. 
-- isTwistOf( E, moduleToKlyachko(variety E, klyachkoToModule(E)) ) should return true
-- F = moduleToKlyachko(variety E , klyachkoToModule E);
-- then F == moduleToKlyachko(variety E, klyachkoToModule(F)) returns true 
klyachkoToModule = method()
-- TODO
klyachkoToModule ToricVectorBundle := E -> (
    X := variety E;
    -- Cox ring of the toric variety
    S := ring X;
    raysX := rays E;
    n := #raysX;
    -- Fine graded ring and base change map
    R := newRing( S, Degrees => entries id_(ZZ^(n)));
    phibase := map (R,S, gens R);
    r := rank E;
    picd := degreeLength S;
    if r == 0 then return S^0;
    -- Twist E so every filtration jump is >= 0, since a jump becomes a monomial 
    jumps := filtrationJumps E;
    offsets := apply(jumps, js -> -(max js)-1);
    E' := if all(offsets, o -> o == 0) then E else twist(E, offsets);
    filtMats := filtrationMatrices E';
    filtJumps :=  filtrationJumps E';

    mj := min flatten filtJumps;
    Mj := max flatten filtJumps;
    -- This is an overkill and porbably makes things slower
    -- Create all the indices to consider
    cands := apply( toList fold( (i,j) -> i**j, (n : set toList(mj..Mj))),i -> toList deepSplice i);
    --correction := apply(offsets, i -> splice{n:i});
    aux := apply(cands , L -> ( 
        monL:= product( apply( n,  i -> (S_i)^(-L_i) ));
       EL := toSequence apply(#L , i ->image (filteredPiece(E', raysX_i, L_i)*monL) );
       EL = phibase**( gens intersect EL);
       --map( R^{r: offsets},R^{ numcols EL : -L - offsets} , EL)
       map( R^r,, EL)
       
       
        )
    );
    (trim image fold((i,j)-> i|j, aux ))**R^{-offsets}

    
    
)

-- A ray is a matrix ZZ^n <-- ZZ^1, so rays can be sorted by assembling them
-- into a matrix and calling "sortColumns".  We sort the rays as in the package
-- Polyhedra, so that changes to the algorithm for computing the hash code of
-- matrices doesn't affect what we do.


-- For some reason it is important for ToricVectorBundles to be able to sort
-- cones. Since cones as keys in hashtables do not work anymore we move the old
-- code for sorting cones here from OldPolyhedra.m2 and implement a method for
-- sorting the new keys.
Cone ? Cone := (C1,C2) -> (
     if C1 == C2 then symbol == else (
     if ambDim C1 != ambDim C2 then ambDim C1 ? ambDim C2 else (
          if dim C1 != dim C2 then dim C1 ? dim C2 else (
          R1 := sort rays C1;
          R2 := sort rays C2;
          if R1 != R2 then (
          R1 = apply(numColumns R1, i -> R1_{i});
          R2 = apply(numColumns R2, i -> R2_{i});
          (a,b) := (set R1,set R2); 
          r := (sort matrix {join(select(R1,i->not b#?i),select(R2,i->not a#?i))})_{0};
          if a#?r then symbol > else symbol <)
          else (
          R1 = linSpace C1;
          R2 = linSpace C2;
          R1 = apply(numColumns R1, i -> R1_{i});
          R2 = apply(numColumns R2, i -> R2_{i});
          (c,d) := (set R1,set R2);
          l := (sort matrix {join(select(R1,i->not d#?i),select(R2,i->not c#?i))})_{0};
          if c#?l then symbol > else symbol <)))))

customConeSort = method()
customConeSort List := L -> (
	L = apply(L, l -> posHull l);
	L = sort L;
	L = apply(L, l -> (rays l, linealitySpace l));
	L
)


raySort = value Polyhedra#"private dictionary"#"raySort"
raySortOfFan = (fan) -> (
    r := rays fan;
    raySort for i from 0 to numColumns r - 1 list r_{i}
    )

-- PURPOSE : Checking for a matrix if it is over ZZ or QQ and returning an error if not
--   INPUT : '(M,msg)',  where 'M' is a matrix and 'msg' is the name of the object 'M' describes
--  OUTPUT : The matrix promoted to QQ if it was over ZZ or QQ, otherwise an error
chkZZQQ = (M,msg) -> (
     R := ring M;
     if R =!= ZZ and R =!= QQ then error("expected matrix of ",msg," to be over ZZ or QQ");
     promote(M,QQ));


-- PURPOSE : Constructing the fan of projective n-space
generateRandomMatrix = method(TypicalValue => Matrix)

--   INPUT : '(m,n,h)',  where 'm' and 'n' are strictly positive integers and 'h' is an integer
--  OUTPUT : An 'm' by 'n' matrix with random entries between 0 and 'h'
generateRandomMatrix (ZZ,ZZ,ZZ) := (m,n,h) -> matrix apply(m, i -> apply(n, j -> random h+1))

--   INPUT : '(m,n,l,h)',  where 'm' and 'n' are strictly positive integers and 'l' 'h' are integers 
--     	    	      	   of which 'l' is the smaller one
--  OUTPUT : An 'm' by 'n' matrix with random entries between 0 and 'h'
generateRandomMatrix (ZZ,ZZ,ZZ,ZZ) := (m,n,l,h) -> matrix apply(m, i -> apply(n, j -> random(l,h)))


-- PURPOSE : Computing the intersection of the images of two matrices
--   INPUT : '(M,N)', two matrices with the same target
--  OUTPUT : a matrix with the minimal generators of the intersection
intersectMatrices = (M,N) -> (
     m := numColumns M;
     N = gens ker(M | N);
     N = N^{0..m-1};
     gens trim image(M*N));

  
-- PURPOSE : Solving the system R*X=F
--   INPUT : '(R,F)',  two matrices over ZZ
--  OUTPUT : a matrix of QQ solutions
systemSolver = (R,F) -> (
     (R1,Lmatrix,Rmatrix) := smithNormalForm lift(R,ZZ);
     F1 := entries(Lmatrix * F);
     Rmatrix * (matrix apply(numRows R1, i -> F1#i / R1_(i,i)) || map(QQ^(numColumns R1 - numRows R1),QQ^(#F1#0),0)))

-- PURPOSE : Constructing the fan of projective n-space
--   INPUT : 'n',  a strictly positive integer
--  OUTPUT : The fan of projective n-space
projectiveSpaceFan = method(TypicalValue => Fan)
projectiveSpaceFan ZZ := n -> (
     if n < 1 then error("The dimension has to be strictly positive.");
     normalFan convexHull (map(ZZ^n,ZZ^n,1)|map(ZZ^n,ZZ^1,0)))


-- PURPOSE : Constructing the fan of the product of n projective 1-spaces
--   INPUT : 'n',  a strictly positive integer
--  OUTPUT : The fan of the product of n projective 1-spaces
pp1ProductFan = method(TypicalValue => Fan)
pp1ProductFan ZZ := n -> (
     if n < 1 then error("The number of PP^1's has to be strictly positive.");
     normalFan hypercube n)


-- PURPOSE : Constructing the fan of the Hirzebruch n-surface
--   INPUT : 'n',  a positive integer
--  OUTPUT : The fan of the Hirzebruch n-surface
hirzebruchFan = method(TypicalValue => Fan)
hirzebruchFan ZZ := n -> hirzebruch n
 
---------------------------------------
-- PRINTING BEHAVIOR
---------------------------------------
-- This is just some adhoc editing, sorry to anybody trying to decipher this!
-- But the basics are: "string | string" will adjoin things horizontally, and
-- "string || string" will adjoin things vertically. Everything done here is
-- gluing strings together with whitespace depending on the width/heights of
-- the matrices here.
-- For those trying to understand, worth pointing out that the HEIGHT of a string
-- is obtained via "length" and NOT "height".
vertSpace = n -> (s := ""; if n == 1 then return "" else for i to n-2 do s = s || ""; s)
horSpace = n -> (s := " "; if n == 0 then return "" else if n == 1 then return s else for i to n-2 do s = s | " "; s)

displayFiltrations = method()
displayFiltrations ToricVectorBundle := E -> (
    filtMats := filtrationMatrices E;
    filtJumps := filtrationJumps E;
    -- here is the range of indices we want to print
    rng := {(min flatten filtJumps)-1, (max flatten filtJumps)+2};
    -- put all of the matrices that appear there into a hash table indexed by rays.
    matTable := hashTable for p in rays E list p => (
        hashTable for i from rng_0 to rng_1 list i => filteredPiece(E,p,i)
        );
    -- to align things properly, we need easy access to the heights of those matrices as strings.
    h' := hashTable for p in rays E list p => max(for M in values matTable#p list length net M);
    -- initialize the string we'll output, as well as a bunch of spacing strings.
    mainStr := "";
    colonStr := " ";
    subsetStr := " ";
    dotsStr := " ... ";
    -- here's where the chaos begins. we're trying to make a grid of filtrations, where the row is
    -- indexed by rays and the column is the index of the filtration. we're going to construct that grid
    -- column by column.
    -- 
    -- this is the first column of that grid. it's just the list of rays, with vertical spacing
    -- added based on the sizes of the matrices appearing in the filtration for that ray.
    -- NOTE: one additional feature of this chunk is that it makes it so that subsetStr and
    -- dotsStr are now fully column strings. by that i mean they are not just single characters,
    -- they have height equal to the height of the whole net at the end, but their vertical
    -- spacing is now perfectly calibrated. so whenever we need to put subsets for our
    -- filtrations, we can just use this single string now.
    w := max for p in rays E list floor(((width net p)-3)/2);
    rayStr := horSpace(w) | "ray" | horSpace(w);
    for p in rays E do (
        -- here's the adjusted vertical spacing depending on the matrices.
        h := floor((h'#p)/2);
        -- for small numbers, this is a very slight adjustment parameter to make things look nicer.
        c := if even h'#p and h'#p != 2 then 1 else 0;
        rayStr = rayStr || vertSpace(h-c+1) || net p || vertSpace(h);
        colonStr = colonStr || vertSpace(h-c+1) || " : " || vertSpace(h);
        dotsStr = dotsStr || vertSpace(h-c+1) || " ... " || vertSpace(h);
        subsetStr = subsetStr || vertSpace(h-c+1) || " ⊃ " || vertSpace(h);
        );
    mainStr = rayStr | colonStr | dotsStr | subsetStr;
    -- this is the main meat of the display. we construct the grid column by column in the same way.
    for i from rng_0 to rng_1 do (
        -- some of the matrices might be smaller than others because of negative signs or numbers, so this
        -- acts as an adjustment parameter to center the matrices.
        w = max({0} | (for p in rays E list ceiling(((width net (matTable#p)#i)-(width net i))/2)));
        -- put the index of the filtration at the top, and then...
        matStr := if max values h' == 1 then horSpace(w) | net i else (horSpace(w) | net i) || vertSpace(1);
        -- start populating the grid entries of the column with the matrices.
        for p in rays E do (
            w' := max({0} | (for q in rays E list floor(((width net (matTable#q)#i)-(width net (matTable#p)#i))/2)));
            h := floor((h'#p)/2);
            c := if even h'#p and h'#p != 2 then 1 else 0;
            if length net (matTable#p)#i == 1 then matStr = matStr || (vertSpace(h-c) || (horSpace(w') | net (matTable#p)#i) || vertSpace(h+1));
            if length net (matTable#p)#i == 2 then matStr = matStr || ((horSpace(w') | net (matTable#p)#i) || vertSpace(2));
            if length net (matTable#p)#i > 2 then matStr = matStr || (((horSpace(w') | net (matTable#p)#i)) || vertSpace(1));
            );
        mainStr = mainStr | matStr | subsetStr
        );
    -- at the very end, all of the filtrations tail off, so we'll add the dots string again.
    mainStr = mainStr | dotsStr;
    mainStr
    )

-- Shamelessly I have copied Greg's kludge from NormalToricVarieties
-- to get printing of maps to look nice.
hasAttribute = value Core#"private dictionary"#"hasAttribute";
getAttribute = value Core#"private dictionary"#"getAttribute";
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary";
expression ToricVectorBundle := E -> (
    if hasAttribute (E, ReverseDictionary) 
    then expression getAttribute (E, ReverseDictionary)
    else net E
    )
net ToricVectorBundle := E -> (
    "ToricVectorBundle of rank " | net rank E | " on " | net variety E
    )


-------------------------------------------
-- TESTS
-------------------------------------------


-------------------------------------------
-- TESTS for the datatype toricVectorBundle
-------------------------------------------
-- Checking toricVectorBundle for Klyachko type -- maybe need to get rid of/modify this becuase it uses the old definition
-*
TEST ///
T = toricVectorBundle(2,pp1ProductFan 2);
assert(T#"ring" === QQ)
assert(T#"filtrationMatricesTable" === hashTable {matrix{{-1},{0}} => map(ZZ^1,ZZ^2,0),matrix{{0},{-1}} => map(ZZ^1,ZZ^2,0),matrix{{1},{0}} => map(ZZ^1,ZZ^2,0),matrix{{0},{1}} => map(ZZ^1,ZZ^2,0)})
assert(T#"baseTable" === hashTable{matrix{{-1},{0}} => map(QQ^2,QQ^2,1),matrix{{0},{-1}} => map(QQ^2,QQ^2,1),matrix{{1},{0}} => map(QQ^2,QQ^2,1),matrix{{0},{1}} => map(QQ^2,QQ^2,1)})
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
L1 = {matrix {{1,0},{0,1}},matrix{{0,1},{1,0}},matrix{{-1,0},{-1,1}}}
L2 = {matrix {{-1,0}},matrix{{-2,-1}},matrix{{0,1}}}
T = toricVectorBundle(2,projectiveSpaceFan 2,L1,L2)
assert(T#"ring" === ZZ)
assert(T#"filtrationMatricesTable" === hashTable {matrix{{-1},{-1}} => matrix{{-1,0}},matrix{{0},{1}} => matrix{{-2,-1}},matrix{{1},{0}} => matrix{{0,1}}})
assert(T#"baseTable" === hashTable {matrix{{-1},{-1}} => matrix {{1,0},{0,1}},matrix{{0},{1}} => matrix{{0,1},{1,0}},matrix{{1},{0}} => matrix{{-1,0},{-1,1}}})
assert(rank T == 2)
assert(T#"dimension of the variety" == 2)
///
*-

-- Tests for basic constructors

-- Test 0
-- Checking trivialBundle
TEST ///
X = toricProjectiveSpace 2
E = trivialBundle(X,4)
assert (rank E == 4)
assert ((filtrationMatrices E)_0 == id_((ring E)^4))
assert ((filtrationJumps E)_0 == toList(4:0))
///

-- Test 1
-- Checking lineBundle
TEST ///
X = hirzebruchSurface 3
D = toricDivisor({5,-3,1,2},X)
L = lineBundle(D)
assert (rank L == 1)
assert (numColumns filteredPiece(L, (rays X)_0, 5) == 1)
assert (numColumns filteredPiece(L, (rays X)_0, 6) == 0)

assert (numColumns filteredPiece(L, (rays X)_1, -3) == 1)
assert (numColumns filteredPiece(L, (rays X)_1, 0) == 0)

L2 = lineBundle(X, {3,4,1,0});
assert (rank L2 == 1)
assert( filtrationJumps L2 =={{3}, {4}, {1}, {0}})
assert((filtrationMatrices L2)_0 == matrix{{1_QQ}})

///
-*
-- Test 2
-- Check for cotangentBundle
TEST ///

T = cotangentBundle hirzebruchSurface 2
assert(ring T === QQ)
assert(filtrationJumps T === {{0,-1},{0,-1},{0,-1},{0,-1}})
assert(filtrationMatrices T === {matrix(QQ,{{1,0},{0,1}}),matrix(QQ,{{0,1},{1,0}}),matrix(QQ,{{0,2},{1/2,1}}),matrix(QQ,{{0,1},{-1,0}})})
assert(rank T == 2)
assert(dim variety T == 2)

T = cotangentBundle(toricProjectiveSpace(1) ** toricProjectiveSpace(1) ** toricProjectiveSpace(1))
assert(filtrationJumps T === {{0,0,-1},{0,0,-1},{0,0,-1},{0,0,-1},{0,0,-1},{0,0,-1}})
assert(filtrationMatrices T === {matrix(QQ,{{-1,0,0},{0,1,0},{0,0,1}}),matrix(QQ,{{1,0,0},{0,1,0},{0,0,1}}),matrix(QQ,{{0,1,0},{-1,0,0},{0,0,1}}),matrix(QQ,{{0,1,0},{1,0,0},{0,0,1}}),matrix(QQ,{{0,1,0},{0,0,1},{-1,0,0}}),matrix(QQ,{{0,1,0},{0,0,1},{1,0,0}})})
assert(rank T == 3)
///
*-


-- Test 2
-- Check for cotangentBundle
TEST ///

T = cotangentBundle hirzebruchSurface 2
assert(ring T === QQ)
assert(filtrationJumps T === {{-1,0},{-1,0},{-1,0},{-1,0}})
assert(filtrationMatrices T === {matrix(QQ,{{1,0},{0,1}}),matrix(QQ,{{0,1},{1,0}}),matrix(QQ,{{0,2},{1/2,1}}),matrix(QQ,{{0,1},{-1,0}})})
assert(rank T == 2)
assert(dim variety T == 2)

T = cotangentBundle(toricProjectiveSpace(1) ** toricProjectiveSpace(1) ** toricProjectiveSpace(1))
assert(filtrationJumps T === {{-1,0,0},{-1,0,0},{-1,0,0},{-1, 0,0},{-1,0,0},{-1,0,0}})
assert(filtrationMatrices T === {matrix(QQ,{{-1,0,0},{0,1,0},{0,0,1}}),matrix(QQ,{{1,0,0},{0,1,0},{0,0,1}}),matrix(QQ,{{0,1,0},{-1,0,0},{0,0,1}}),matrix(QQ,{{0,1,0},{1,0,0},{0,0,1}}),matrix(QQ,{{0,1,0},{0,0,1},{-1,0,0}}),matrix(QQ,{{0,1,0},{0,0,1},{1,0,0}})})
assert(rank T == 3)
///

-- Test 3
-- Checking tangentBundle for Klyachko
TEST ///
T = tangentBundle hirzebruchSurface 3
assert(ring T === QQ)
assert(filtrationJumps T == {{1, 0}, {1, 0}, {1, 0}, {1, 0}})
assert(filtrationMatrices T == {map(QQ^2,QQ^2,{{1, 0}, {0, 1}}),map(QQ^2,QQ^2,{{0, 1}, {1, 0}}),map(QQ^2,QQ^2,{{-1, 1/3}, {3,
      0}}),map(QQ^2,QQ^2,{{0, 1}, {-1, 0}})})
assert(rank T == 2)
assert(dim variety T == 2)
///

-- Tests for getter functions

-- Test 4
--Test for ring
TEST ///
X = toricProjectiveSpace 2;
T1 = trivialBundle(X,2);
assert(ring T1 === QQ)
Y = hirzebruchSurface(3, CoefficientRing=>ZZ/101);
T2 = cotangentBundle(Y);
assert(ring T2 === ZZ/101)
///

-- Tests for operations

-- Test 5
--Test direct sum
TEST ///
-- old test
X = toricProjectiveSpace 3
T1 = tangentBundle X
T2 = lineBundle(X, {1,7,5,3})
T = T1 ++ T2

assert(ring T === QQ)
assert(filtrationJumps T == {{1, 0, 0, 1}, {1, 0, 0, 7}, {1, 0, 0, 5}, {1, 0, 0, 3}})
assert(filtrationMatrices T == {map(QQ^4,QQ^4,{{-1, 0, 0, 0}, {-1, 1, 0, 0}, {-1, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{1, 0, 0,
       0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, 1,
       0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 1, 0, 0}, {0, 0, 1, 0}, {1, 0, 0, 0}, {0, 0, 0, 1}})})
assert(rank T == 4)
assert(dim variety T == 3)
assert(T == directSum{T1,T2})

Y = hirzebruchSurface 3
T1 = cotangentBundle Y
T2 = tangentBundle Y
T = T1 ++ T2
assert(ring T === QQ)
assert(filtrationJumps T == {{-1, 0, 1, 0}, {-1, 0,1, 0}, {-1, 0,1, 0}, {-1, 0, 1, 0}})
-- assert(filtrationJumps T == {{0, -1, 1, 0}, {0, -1, 1, 0}, {0, -1, 1, 0}, {0, -1, 1, 0}})
assert(filtrationMatrices T == {map(QQ^4,QQ^4,{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 1, 0,
        0}, {1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, 1, 0}}),map(QQ^4,QQ^4,{{0, 3, 0, 0}, {1/3, 1, 0, 0}, {0, 0,
        -1, 1/3}, {0, 0, 3, 0}}),map(QQ^4,QQ^4,{{0, 1, 0, 0}, {-1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, -1, 0}})})
assert(rank T == 4)
assert(dim variety T == 2)


-- new test
X = toricProjectiveSpace 2;
T1 = trivialBundle(X,2);
T2 = tangentBundle(X);
T= T1++T2;
assert( rank(T) == 4)
assert( rank(T) == rank (T1) + rank (T2))
assert( filteredPiece(T, {-1,-1},0) == matrix(QQ, {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, -1, -1}, {0, 0, -1, 0}} ))
assert( variety(T)=== variety(T2) )
assert(filtrationJumps(T)=={{0, 0, 1, 0}, {0, 0, 1, 0}, {0, 0, 1, 0}} )
assert(filtrationMatrices(T) == {matrix(QQ, {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, -1, -1}, {0, 0, -1, 0}}), matrix(QQ, {{1, 0, 0, 0},{0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}), matrix(QQ, {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 0, 1},{0, 0, 1, 0}} )} )
///

-- Test 6
--Test tensor product
TEST ///
-- old test
X = toricProjectiveSpace 1 ** toricProjectiveSpace 1
T1 = tangentBundle X
T2 = cotangentBundle X
T = T1 ** T2
assert(ring T === QQ)
assert(filtrationJumps T == {{0, 1, -1, 0}, {0, 1, -1, 0}, {0, 1, -1, 0}, {0, 1, -1, 0}})
assert(filtrationMatrices T == {map(QQ^4,QQ^4,{{1, 0, 0, 0}, {0, -1, 0, 0}, {0, 0, -1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{1, 0, 0,0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 0, 0, 1}, {0, 0, -1, 0}, {0, -1,        0, 0}, {1, 0, 0, 0}}),map(QQ^4,QQ^4,{{0, 0, 0, 1}, {0, 0, 1, 0}, {0, 1, 0, 0}, {1, 0, 0, 0}})})
assert(rank T == 4)
assert(dim variety T == 2)

Y = hirzebruchSurface 2
T1 = tangentBundle Y
T2 = lineBundle(Y, {5,1,7,3})
T2 = T2 ++ T2
T = T1 ** T2
assert(ring T === QQ)
assert(filtrationJumps T == {{6, 6, 5, 5}, {2, 2, 1, 1}, {8, 8, 7, 7}, {4, 4, 3, 3}})
assert(filtrationMatrices T == {map(QQ^4,QQ^4,{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 0, 1,0}, {0, 0, 0, 1}, {1, 0, 0, 0}, {0, 1, 0, 0}}),map(QQ^4,QQ^4,{{-1, 0, 1/2, 0}, {0, -1, 0, 1/2}, {2,0, 0, 0}, {0, 2, 0, 0}}),map(QQ^4,QQ^4,{{0, 0, 1, 0}, {0, 0, 0, 1}, {-1, 0, 0, 0}, {0, -1, 0, 0}})})
assert(rank T == 4)
assert(dim variety T == 2)

-- new test
X = toricProjectiveSpace 2;
T1 = trivialBundle(X,3);
T2 = tangentBundle(X);
T= T1**T2;
assert( rank(T) == 6)
assert( rank(T) == rank (T1)* rank (T2))
assert( filteredPiece(T, {-1,-1},1) ==  matrix(QQ, {{-1, 0, 0}, {-1, 0, 0}, {0, -1, 0}, {0, -1, 0}, {0, 0, -1}, {0, 0, -1}}))
assert( variety(T)=== variety(T2) )
assert(filtrationJumps(T)=={{1, 0, 1, 0, 1, 0}, {1, 0, 1, 0, 1, 0}, {1, 0, 1, 0, 1, 0}})
assert(filtrationMatrices(T) ==  {matrix(QQ, {{-1, -1, 0, 0, 0, 0}, {-1, 0, 0, 0, 0, 0}, {0, 0, -1, -1, 0, 0}, {0, 0, -1, 0, 0,      0}, {0, 0, 0, 0, -1, -1}, {0, 0, 0, 0, -1, 0}}), matrix(QQ, {{1, 0, 0, 0, 0, 0}, {0, 1, 0, 0, 0,  0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 0, 0}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}), matrix(QQ,      {{0, 1, 0, 0, 0, 0}, {1, 0, 0, 0, 0, 0}, {0, 0, 0, 1, 0, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0,      0, 0, 1}, {0, 0, 0, 0, 1, 0}})} )
///

-- Test 7
-- Checking dual for Klyachko
TEST ///
-- old test
X = toricProjectiveSpace 3
T = dual lineBundle(X, {1,4,3,2})
assert(ring T === QQ)
assert(filtrationJumps T == {{-1}, {-4}, {-3}, {-2}})
assert(filtrationMatrices T == {map(QQ^1,QQ^1,{{1}}),map(QQ^1,QQ^1,{{1}}),map(QQ^1,QQ^1,{{1}}),map(QQ^1,QQ^1,{{1}})})
assert(rank T == 1)
assert(dim variety T == 3)

T1 = tangentBundle X
T = dual (T1 ++ T)
assert(ring T === QQ)
assert(filtrationJumps T == {{-1, 0, 0, 1}, {-1, 0, 0, 4}, {-1, 0, 0, 3}, {-1, 0, 0, 2}})
assert(filtrationMatrices T == {map(QQ^4,QQ^4,{{-1, -1, -1, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{1, 0,
        0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0,
        1, 0}, {0, 0, 0, 1}}),map(QQ^4,QQ^4,{{0, 1, 0, 0}, {0, 0, 1, 0}, {1, 0, 0, 0}, {0, 0, 0, 1}})})
assert(rank T == 4)
assert(dim variety T == 3)
///

-- Test 8
-- Checking exteriorPower for Klyachko
TEST ///
T = cotangentBundle hirzebruchSurface 3
T = exteriorPower(T,2)
assert(ring T == ideal(1_QQ))

assert(filtrationJumps T == {{-1}, {-1}, {-1}, {-1}})
assert(filtrationMatrices T == {map(QQ^1,QQ^1,{{1}}),map(QQ^1,QQ^1,{{-1}}),map(QQ^1,QQ^1,{{-1}}),map(QQ^1,QQ^1,{{1}})})
assert(rank T == 1)
assert(dim variety T == 2)

T = tangentBundle toricProjectiveSpace 3
T = exteriorPower(T,2)
assert(ring T == ideal(1_QQ))

assert(filtrationJumps T == {{1, 1, 0}, {1, 1, 0}, {1, 1, 0}, {1, 1, 0}})
assert(filtrationMatrices T == {map(QQ^3,QQ^3,{{-1, 0, 0}, {0, -1, 0}, {1, -1, 1}}),map(QQ^3,QQ^3,{{1, 0, 0}, {0, 1, 0}, {0, 0,
      1}}),map(QQ^3,QQ^3,{{-1, 0, 0}, {0, 0, 1}, {0, 1, 0}}),map(QQ^3,QQ^3,{{0, 0, 1}, {-1, 0, 0}, {0, -1,
      0}})})
assert(rank T == 3)
assert(dim variety T == 3)

X = hirzebruchSurface 2;
E = tangentBundle X;
assert(exteriorPower(E,1) == E)
assert(rank exteriorPower(E++E,2) == 6)
D = toricDivisor({1,2,4,5},X)
L = lineBundle(D)
E1 = exteriorPower(E++L, 2);
E2 = (exteriorPower(E,0)**exteriorPower(L,2))++(exteriorPower(E,1)**exteriorPower(L,1))++(exteriorPower(E,2)**exteriorPower(L,0))
assert(areIsomorphic(E1,E2))
///

-- Test 9
-- Checking symmetricPower for Klyachko
TEST ///
T = tangentBundle toricProjectiveSpace 3
T = symmetricPower(T,2)
assert(ring T === QQ)
assert(filtrationJumps T == {{2, 1, 1, 0, 0, 0}, {2, 1, 1, 0, 0, 0}, {2, 1, 1, 0, 0, 0}, {2, 1, 1, 0, 0, 0}})
assert(filtrationMatrices T == {map(QQ^6,QQ^6,{{1, 0, 0, 0, 0, 0}, {2, -1, 0, 0, 0, 0}, {2, 0, -1, 0, 0, 0}, {1, -1, 0, 1, 0, 0},
      {2, -1, -1, 0, 1, 0}, {1, 0, -1, 0, 0, 1}}),map(QQ^6,QQ^6,{{1, 0, 0, 0, 0, 0}, {0, 1, 0, 0, 0, 0},
      {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 0, 0}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}),map(QQ^6,QQ^6,{{0,
      0, 0, 1, 0, 0}, {0, 1, 0, 0, 0, 0}, {0, 0, 0, 0, 1, 0}, {1, 0, 0, 0, 0, 0}, {0, 0, 1, 0, 0, 0}, {0,
      0, 0, 0, 0, 1}}),map(QQ^6,QQ^6,{{0, 0, 0, 1, 0, 0}, {0, 0, 0, 0, 1, 0}, {0, 1, 0, 0, 0, 0}, {0, 0, 0,
      0, 0, 1}, {0, 0, 1, 0, 0, 0}, {1, 0, 0, 0, 0, 0}})})
assert(rank T == 6)
assert(dim variety T == 3)
///

-- Test 10
--Checking areIsomorphic
--first test, check trivial bundles of different ranks are not isomorphic
TEST ///
PP2 = toricProjectiveSpace 2;
T1 = trivialBundle(PP2,2);
T2 = trivialBundle(PP2,4);
assert not areIsomorphic(T1,T2)
--check that line bundles on different divisors are not isomorphic
D0 = toricDivisor({1,0,0},PP2);
E1 = lineBundle(D0);
D1 = toricDivisor({0,1,0},PP2);
E2 = lineBundle(D1);
assert not areIsomorphic(E1,E2)
--next checking bundles that are isomorphic
PP3 = toricProjectiveSpace 3;
D = toricDivisor({1,2,-1,0},PP3);
L1 = lineBundle D;
triv = trivialBundle(PP3,1);
L2 = twist(triv,{1,2,-1,0});
assert areIsomorphic(L1,L2)
--checking isomorphic if the same bundle but different bases
T3 = trivialBundle(PP3,3);
basisMat = matrix{{1,0,0},{1,1,0},{1,0,1}};
p = #(rays T3);
filtMat = apply(p, i -> basisMat);
jumpsT3 = filtrationJumps T3;
T4 = toricVectorBundle(PP3,filtMat,jumpsT3);
assert areIsomorphic(T3,T4)
--checking isomorphic for changing basis filtration matrices in different ways
TT3 = trivialBundle(PP3,3);
basisMat0 = (filtrationMatrices TT3)#0 * (matrix{{1,0,0},{1,1,0},{1,0,1}});
basisMat1 = (filtrationMatrices TT3)#1 * (matrix{{1,0,1},{0,1,1},{0,1,0}});
basisMat2 = (filtrationMatrices TT3)#2 * (matrix{{1,-1,1},{-1,0,1},{0,1,-1}});
basisMat3 = (filtrationMatrices TT3)#3;
T = toricVectorBundle(PP3,{basisMat0,basisMat1,basisMat2,basisMat3},filtrationJumps TT3);
assert areIsomorphic(TT3,T)
assert areIsomorphic(T,TT3)

X = toricProjectiveSpace 3;
L1 = lineBundle(X, {1,2,3,4} );
L2 = lineBundle(X ,{0,1,0,2});
T1 = L1++L2;
T2 = L2++L1;

assert areIsomorphic( T1, T2)
assert (map isomorphism( T1, T2) == matrix( ring T1,{{0, 1}, {1, 0}} ))


-- Checks that the 2nd method works
T1 = (tangentBundle X ** lineBundle(X, {2,-3,4,3})) ++ lineBundle(X_2 + X_3)
displayFiltrations T1

T2 =  lineBundle(X_2 + X_3)++ (lineBundle(X, {2,-3,4,3})** tangentBundle X ) 
displayFiltrations T2

assert areIsomorphic (T1,T2)


-- Checks that the 3rd method works
T1 = tangentBundle X;
T2 = toricVectorBundle( X, filtrationMatrices T1, {{1,0,0},{0,1,0},{0,0,1},{0,1,0}})

assert areIsomorphic (T1,T2)

///

-- Test 11
--Test for isomorphism
TEST ///
PP3 = toricProjectiveSpace 3;
D = toricDivisor({1,2,-1,0},PP3);
L1 = lineBundle D;
triv = trivialBundle(PP3,1);
L2 = twist(triv,{1,2,-1,0});
conjIsoL1L2 = map(L2,L1,id_((ring L1)^(rank L1)));
assert (isomorphism(L1,L2) === conjIsoL1L2)
conjIsoL2L1 = map(L1,L2,id_((ring L2)^(rank L2)));
assert (isomorphism(L2,L1) === conjIsoL2L1)
--same bundle but different bases
T3 = trivialBundle(PP3,3);
basisMat = matrix{{1,0,0},{1,1,0},{1,0,1}};
p = #(rays T3);
filtMat = apply(p, i -> basisMat);
jumpsT3 = filtrationJumps T3;
T4 = toricVectorBundle(PP3,filtMat,jumpsT3);
conjIsoT3T4 = map(T4,T3,id_((ring T3)^(rank T3)));
assert (isomorphism(T3,T4) === conjIsoT3T4)
conjIsoT4T3 = map(T3,T4,id_((ring T4)^(rank T4)));
assert (isomorphism(T4,T3) === conjIsoT4T3)

-- Mahrud's example
X = toricProjectiveSpace 2;
E1 = toricVectorBundle(X,{matrix {{-1,-1},{-1,0}}, matrix {{1,0},{0,1}}, matrix {{0,1},{1,0}}}, {{1,0},{1,0},{1,0}})
E2 = toricVectorBundle(X,{matrix {{-1,0},{-1,-1}}, matrix {{0,1},{1,0}}, matrix {{1,0},{0,1}}}, {{1,0},{1,0},{1,0}})
assert(areIsomorphic(E1,E2) and areIsomorphic(E2,E1))
assert(map isomorphism(E1,E2) == matrix(ring E1, {{0,1},{1,0}}))

-- here's another random example
Y = hirzebruchSurface 2;
E1' = tangentBundle Y ++ tangentBundle Y;
M = matrix(ring E1', {{1,1,0,2},{0,1,1,1},{0,1,0,-1},{0,0,0,1}});
filtmats = apply(filtrationMatrices E1', m -> M * m)
E2' = toricVectorBundle(Y,filtmats, filtrationJumps E1')
assert(map isomorphism(E1',E2') == M)
///

-- No test for isTwistOf?

-- Tests for cohomological computations

-- Test 12
-- Checking eulerChi
TEST ///
T = tangentBundle hirzebruchSurface 3;
assert(eulerChi(matrix {{0},{0}},T) == 2)
assert(eulerChi T == 6)

T = cotangentBundle toricProjectiveSpace 4;
assert(eulerChi T == -1) -- eulerChi T == 2 :(
///

-- Test 13
-- Checking cohomology for Klyachko
TEST ///
T1 = trivialBundle(X = toricProjectiveSpace 1 ** toricProjectiveSpace 1, 2)
assert(sort degrees cohomology(0,T1) == sort degrees (grRing T1)^{{0,0},{0,0}})
assert(sort degrees cohomology(1,T1) == sort degrees (grRing T1)^0)
assert(sort degrees cohomology(2,T1) == sort degrees (grRing T1)^0)
T2 = tangentBundle X
assert(sort degrees cohomology(0,T2,matrix{{0},{0}}) == sort degrees (grRing T2)^{{0,0},{0,0}})
assert(sort degrees cohomology(0,T2,matrix{{1},{1}}) == sort degrees (grRing T2)^0)
assert(sort degrees cohomology(0,T2) == sort degrees (grRing T2)^{{1,0},{0,1},{0,0},{0,0},{0,-1},{-1,0}})
assert(sort degrees cohomology(1,T2) == sort degrees (grRing T2)^0)
assert(sort degrees cohomology(2,T2) == sort degrees (grRing T2)^0)
T3 = tangentBundle(Y = hirzebruchSurface 3 ** toricProjectiveSpace 1)
assert(sort degrees cohomology(0,T3) == sort degrees (grRing T3)^{{0, 0, 1}, {1, 0, 0}, {0, 0, 0}, {0, 0, 0}, {0, 0, 0}, {-1, 0, 0}, {0, 0, -1}, {0, -1, 0}, {-1, -1, 0}, {-2, -1, 0}, {-3, -1, 0}})
assert(sort degrees cohomology(1,T3) == sort degrees (grRing T3)^{{2, 1, 0}, {1, 1, 0}})
assert(sort degrees cohomology(2,T3) == sort degrees (grRing T3)^0)
assert(sort degrees cohomology(3,T3) == sort degrees (grRing T3)^0)
///

-- Test 14
-- Checking deltaE for Klyachko
TEST ///
T = trivialBundle(toricProjectiveSpace(2),3)
assert(deltaE T == convexHull matrix{{0},{0}})
T = tangentBundle toricProjectiveSpace 2
assert(deltaE T == convexHull matrix {{-1,2,-1},{-1,-1,2}})
T = cotangentBundle(toricProjectiveSpace(1) ** toricProjectiveSpace(1) ** toricProjectiveSpace(1))
assert(deltaE T == convexHull matrix {{-1,1,-1,1,-1,1,-1,1},{-1,-1,1,1,-1,-1,1,1},{-1,-1,-1,-1,1,1,1,1}})
///

-- Test 15
-- Checking isGeneral
TEST ///
T = tangentBundle (toricProjectiveSpace 1 ** toricProjectiveSpace 1 ** toricProjectiveSpace 1)
assert isGeneral T

L1 = {{1,0},{1,0},{-1,-1},{1,0}}
L2 = {matrix{{1,0},{0,1}},matrix{{-1,0},{0,1}},matrix{{-1,1},{0,-1}},matrix{{1,1},{0,1}}}
T = toricVectorBundle(hirzebruchSurface 3,L2,L1)

assert not isGeneral T

///

-- Test 16
-- Checking twist
TEST ///
T = tangentBundle toricProjectiveSpace 3
L = {1,-4,3,-2}
T = twist(T,L)
assert(ring T === QQ)
assert(filtrationJumps T == {{2, 1, 1}, {-3, -4, -4}, {4, 3, 3}, {-1, -2, -2}})
assert(filtrationMatrices T == {map(QQ^3,QQ^3,{{-1, 0, 0}, {-1, 1, 0}, {-1, 0, 1}}),map(QQ^3,QQ^3,{{1, 0, 0}, {0, 1, 0}, {0, 0,
       1}}),map(QQ^3,QQ^3,{{0, 1, 0}, {1, 0, 0}, {0, 0, 1}}),map(QQ^3,QQ^3,{{0, 1, 0}, {0, 0, 1}, {1, 0,
       0}})})
assert(rank T == 3)
assert(dim variety T == 3)

X = toricProjectiveSpace 2;
T1 = tangentBundle(X);
L = lineBundle(toricDivisor({1,2,-1},X));
T = twist(T1, {1,2,-1} );
assert( rank(T) == 2)
assert( variety(T)=== X )
assert(filtrationJumps(T)=={{2, 1}, {3, 2}, {0, -1}})
assert(filtrationMatrices(T) == {matrix(QQ, {{-1, -1}, {-1, 0}}), matrix(QQ ,{{1, 0}, {0, 1}}), matrix(QQ, {{0, 1}, {1, 0}})})
assert(areIsomorphic(T, T1**L) )
///

-- Tests for maps

-- Test 17
--Test for ToricVectorBundleMap
TEST ///
PP3 = toricProjectiveSpace 3;
trivPP3 = trivialBundle(PP3,3);
tangPP3 = tangentBundle(PP3);
--creates a map (maybe not well defined)
M = matrix(ring trivPP3, {{1,0,1},{0,1,0},{1,1,0}});
tvbMap = map(trivPP3,tangPP3,M)
assert(source tvbMap === tangPP3)
assert(target tvbMap === trivPP3)
assert(map tvbMap === M)
--maps from different rank bundles

///

-- Test 18
--Test for isWellDefined for ToricVectorBundleMap
TEST ///
X = toricProjectiveSpace 3;
E = trivialBundle(X, 3);
F = trivialBundle(X, 5);
--test a map that is well defined
assert (isWellDefined map(F, E, matrix(ring E, {{1,0,0},{0,1,0},{0,0,1},{0,0,0},{0,0,0}})))

D1 = toricDivisor({1,2,-1,0},X);
D2 = toricDivisor({3,-1,2,0},X);
D3 = toricDivisor({5,0,1,0},X);
L1 = lineBundle(D1)
L2 = lineBundle(D2)
L3 = lineBundle(D3)
--test a map that is not well defined
assert (not isWellDefined map(E, L1 ++ L2 ++ L3, id_((ring E)^3)))
///

-- Tests for isInjective and isSurjective
-- Test 19
TEST ///
X = toricProjectiveSpace 2
D1 = toricDivisor({1,0,0},X)
D2 = toricDivisor({0,1,0},X)
D3 = toricDivisor({0,0,1},X)

L1 = lineBundle(D1)
L2 = lineBundle(D2)
L3 = lineBundle(D3)

E1 = trivialBundle(X,1)
E2 = L1 ++ L2 ++ L3

f = map(E2, E1, matrix(QQ,{{1},{1},{1}}))

Y = toricProjectiveSpace 3
F1 = trivialBundle(X,5)
F2 = trivialBundle(X,3)

g = map(F2,F1,matrix(ring F1, {{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0}}))


assert (isInjective f)
assert (not isInjective g)
assert (isSurjective g)
assert (not isSurjective f)
///

-- Test 20
-- Test for image, kernel and cokernel
TEST ///
X = toricProjectiveSpace(3, CoefficientRing=> ZZ/101);
TX = tangentBundle X;
triv = trivialBundle(X,1);
sumoflbs = lineBundle X_0 ++ lineBundle X_1 ++ lineBundle X_2 ++ lineBundle X_3;
f = map(sumoflbs,triv,matrix(ZZ/101,{{1},{1},{1},{1}}));
g = map(TX,sumoflbs, transpose sub(matrix rays X,ZZ/101));
-- Image
imf = image f;
kg = ker g;
assert(areIsomorphic(imf , kg))
assert( rank(imf)== 1)
assert( variety imf === X)
assert( filtrationJumps (imf) =={{0}, {0}, {0}, {0}} )
assert( filtrationMatrices imf == {matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}})
img= image g;
assert ( img == target g)


-- Kernel
assert( rank(kg)== 1)
assert( variety kg === X)
assert( filtrationJumps (kg) =={{0}, {0}, {0}, {0}} )
assert( filtrationMatrices kg == {matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}, matrix {{1_(ZZ/101)}}})
kf = ker f;
assert ( ker f == trivialBundle(X,0))

-- Cokernel
CKf = coker f;
assert(areIsomorphic(CKf , TX))
assert( rank(CKf)== 3)
assert( variety CKf === X)
-- The next two tests may have to be changed if the way of computing the filtered pieces changes
assert( filtrationJumps( CKf)=={{1, 0, 0}, {1, 0, 0}, {1, 0, 0}, {1, 0, 0}} )
assert( filtrationMatrices(CKf)=={matrix(ZZ/101, {{-1, 1, 0}, {-1, 0, 1}, {-1, 0, 0}}), matrix(ZZ/101, {{1, -1, 0}, {0, -1, 1}, {0, -1, 0}}), matrix(ZZ/101, {{0, -1, 1}, {1, -1, 0}, {0, -1, 0}}), matrix(ZZ/101, {{0, -1, 1}, {0, -1, 0}, {1, -1, 0}}) } )
-- g is surjective
CKg = coker g;
assert(CKg== trivialBundle(X,0) )




E = tangentBundle hirzebruchSurface 2;
m = id_(QQ^2);
z = transpose matrix {{0,0,0,0}};
M = z | z | (m || m);
f = map(E ++ E, E ++ E, transpose M)
assert(image f == E)
///

-- Test 21
--Checking direct sum of maps
TEST ///
X = toricProjectiveSpace 1
E0 = lineBundle(X,{0,0})
E1 = lineBundle(X,{1,0})
E01 = lineBundle(X,{-1,0})
f = map(E1,E0,matrix(QQ,{{4}}))
g = map(E0,E01,matrix(QQ,{{7}}))
h = f ++ g
assert(h.map == matrix(QQ,{{4,0},{0,7}}))
///

-- Test 22
--Checking tensor of maps
TEST ///
X = toricProjectiveSpace 1
E0 = lineBundle(X,{0,0})
E1 = lineBundle(X,{1,0})
E01 = lineBundle(X,{-1,0})
E2 = lineBundle(X,{2,0})
f = map(E1 ++ E0, E0 ++ E01, matrix(QQ,{{4,0},{0,7}}))
g = map(E2, E0, matrix(QQ,{{3}}))
h = f ** g
assert(h.map == matrix(QQ,{{12,0},{0,21}}))
///

-- Tests for Weil decorations
-- Test 23
--Checking weilDecoration on the direct sum of the tangent bundle with a line bundle on P2.
TEST ///
M = toricProjectiveSpace 2;
V = tangentBundle M++lineBundle(M_1);
W = weilDecoration V;
(strats, divs) = toSequence transpose ((strata W)/toList)
assert(strats/rank == {1,1,2,3})
assert(divs == {M_2, M_0, M_1, M_1 - M_1})
E = weilToKlyachko(M,W)
assert(E == V)
///

-- Test 24
TEST ///
X = toricProjectiveSpace 2
T1 = tangentBundle X
M1 = klyachkoToModule T1
T2 = moduleToKlyachko (X, M1)
M2 = klyachkoToModule T2 
T3 = moduleToKlyachko (X, M2)
assert( T3 == T1)
///


--Test 25
--Test for toricDivisor ? toricDivisor, gcd and lcm
TEST ///
--toricDivisor ? toricDivisor
PP2=toricProjectiveSpace 2;
D1=toricDivisor({2,5,-7},PP2);
D2=toricDivisor({2,5,-7},PP2);
--check ==
assert((D2?D1) === symbol ==)
D3=toricDivisor({2,4,-7},PP2);
--check <
assert((D3?D1) === symbol <)
D4=toricDivisor({2,5,-6},PP2);
--check >
assert((D4?D1) === symbol >)
D5=toricDivisor({2,4,-6},PP2);
--check incomparable
assert((D5?D1) === symbol incomparable)


--gcd
D6=toricDivisor({2,4,-7},PP2);
assert(gcd(D1,D5) == D6)
--lcm
D7=toricDivisor({2,5,-6},PP2);
assert(lcm(D1,D5) == D7)

///

load "KaneyamaTests.m2"

-- Test ??
-- Checking isWellDefined TODO : I think this was intended for Klyachko type originally
TEST ///
T = toricVectorBundle(2,pp1ProductFan 2)
T1 = addBase(T,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
assert isWellDefined T1
T = toricVectorBundle(1,normalFan crossPolytope 3)
L = apply({2,1,1,2,2,1,1,2}, i -> matrix {{i}});
T = addFiltration(T,L)
assert not isWellDefined T
///


---------------------------------------------------------------------------
-- TESTS for PositivityToricBundles
---------------------------------------------------------------------------
-- We test against the examples from [RJS]
-- CAVEAT: 1) The data is copied from [RJS], but many signs are different,
--         as [RJS] and ToricVectorBundle (and therefore PositivityToricBundles)
--         follow different sign conventions.
--         2) When setting up the vector bundles using ToricVectorBundles,
--         I have no direct influence on the (internal) order of rays.
--         Fortunately, it seems that the order is always chosen in the same way.
--         If this changes at some point in the future, all tests will fail.

-- Test 0
TEST ///
-- This is [RJS, Example 3.7]
-- auxiliary methods
X = toricProjectiveSpace 1 ** toricProjectiveSpace 1
V = trivialBundle(X,3);
rays V
-- output: {{-1, 0}, {1, 0}, {0, -1}, {0, 1}}

Vbasis = { 
 matrix{{1_QQ,1,0},{0,0,1},{1,0,0}},   -- for (-1,0)
 matrix{{1_QQ,1,0},{1,0,0},{0,0,1}}, -- for (1,0)
 matrix{{0_QQ,0,1},{1,0,0},{0,1,0}},   -- for (0,-1)
 matrix{{0_QQ,0,1},{1,0,0},{0,1,0}}   -- for (0,1)
 };
Vfiltration = {
 {-1,0,1},   -- for (-1,0)
 {-1,0,1},  -- for (1,0)
 {-2,-1,0},  -- for (0,-1)
 {-2,-1,0}  -- for (0,1)
 };
V = toricVectorBundle(X, Vbasis, -1*Vfiltration) 

p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{-1,0}}, set {}, set {{0,0}}, set {{1,0}}  } );


c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{-1,0},{0,-2},{1,-1}},
        set {{1,0},{-1,-2},{0,-1}},
        set {{1,0},{-1,2},{0,1}},
        set {{0,2},{-1,0},{1,1}} } );
///

-- Test 1
TEST ///
-- This is [RJS, Example 3.8] for d=2
X = toricProjectiveSpace 2
V = tangentBundle X


p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{0,0},{-1,1},{-1,0}},
        set {{0,0},{1,-1},{0,-1}}, 
        set {{0,0},{1,0},{0,1}} } );


c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{1,0},{1,-1}},
        set {{-1,1},{0,1}},
        set {{-1,0},{0,-1}} } );

assert(isGloballyGenerated V);
assert(isVeryAmple V);

assert(isNef V);
assert(isAmple V);
///



-- Test 2
TEST ///
-- This is [RJS, Example 3.8] for d=3
X = toricProjectiveSpace 3;
V = tangentBundle(X);


p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{0,0,0},{-1,0,1},{-1,1,0},{-1,0,0}},
        set {{0,0,0},{1,-1,0},{0,-1,1},{0,-1,0}}, 
        set {{0,0,0},{1,0,-1},{0,1,-1},{0,0,-1}}, 
        set {{0,0,0},{1,0,0},{0,1,0},{0,0,1}} } );


c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{1,0,0},{1,-1,0},{1,0,-1}},
        set {{0,1,0},{-1,1,0},{0,1,-1}},
        set {{0,0,1},{-1,0,1},{0,-1,1}},
        set {{-1,0,0},{0,-1,0},{0,0,-1}} } );

assert(isGloballyGenerated V);
assert(isVeryAmple V);

assert(isNef V);
assert(isAmple V);
///

-- Test 3
TEST ///
-- This is [RJS, Example 4.2] 
-- auxiliary methods
X = toricProjectiveSpace 2
Vbasis = { 
 matrix{{1,0,0},{-1,1,0},{0,-1,1}},  -- for (-1,-1)
 matrix{{1,0,0},{0,1,0},{0,0,1}},  -- for (1,0)
 matrix{{0,0,1},{0,1,0},{1,0,0}}    -- for (0,1)
 }

Vfiltration = {
 matrix{{-3,-2,1}},  -- for (-1,-1)
 matrix{{-4,0,1}}, -- for (1,0)
 matrix{{-3,0,2}}   -- for (0,1)
}
Vfiltration = -flatten (Vfiltration/entries)
V = toricVectorBundle(X, Vbasis, Vfiltration)


p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{-3,2},{-4,2},{-4,3}},
        set {{1,2},{0,2},{0,3}},
        set {},
        set {{2,0},{1,0},{1,1}},
        set {{2,-3},{1,-3},{1,-2}} } );


c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{1,2},{2,0},{2,-3}},
        set {{-4,3},{0,3},{1,1}},
        set {{-4,2},{0,0},{1,-3}} } );

assert(not isGloballyGenerated V);
assert(not isVeryAmple V);

assert(isNef V);
assert(isAmple V);
///



-- Test 4
TEST ///
-- This is [RJS, Example 4.4] 
-- auxiliary methods

X = hirzebruchSurface 1
Vbasis = { 
 matrix{{1,0},{0,1}},  -- for (1,0)
 matrix{{1,0},{0,1}},   -- for (0,1)
 matrix{{0,1},{1,0}},   -- for (-1,1)
 matrix{{1,1},{1,0}}   -- for (0,-1)
}

Vfiltration = {
 matrix{{-4,2}},  -- for (1,0)
 matrix{{-3,-2}},  -- for (0,1)
 matrix{{-5,0}},   -- for (-1,1)
 matrix{{-3,1}}   -- for (0,-1)
}
Vfiltration = -flatten (Vfiltration/entries)
V = toricVectorBundle(X, Vbasis, Vfiltration)

p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{-1,-1},{-3,-3},{-4,-3},{-4,-1}},
        set {{3,3},{2,2},{2,3}},
        set {{4,-1},{3,-2},{2,-2},{2,-1}} } );

c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{2,-2},{-4,-3}},
        set {{3,-2},{-3,-3}},
        set {{4,-1},{3,3}},
        set {{2,3},{-4,-1}} } );

assert(isGloballyGenerated V);
assert(isVeryAmple V);

assert(isNef V);
assert(isAmple V);
///


-- Test 5
TEST ///
-- This is [RJS, Example 6.4] 
-- auxiliary methods
X = toricProjectiveSpace 2

Vbasis = { 
 matrix{{1,0,0},{-1,1,0},{0,-1,1}},  -- for (-1,-1)
 matrix{{1,0,0},{0,1,0},{0,0,1}},  -- for (1,0)
 matrix{{0,0,1},{0,1,0},{1,0,0}}    -- for (0,1)
 }; 

Vfiltration = {
 matrix{{-4,-3,-1}}, -- for (-1,-1)
 matrix{{-2,1,2}},  -- for (1,0)
 matrix{{-2,0,2}}   -- for (0,1)
 };

Vfiltration = -flatten (Vfiltration/entries)
V = toricVectorBundle(X, Vbasis, Vfiltration)

p = parliament V;
assert( 
  set apply(values p, q -> set entries transpose lift(vertices q,ZZ)) ===
  set { set {{-1,2},{-2,2},{-2,3}},
        set {{2,2},{1,2},{1,3}},
        set {{1,0}},
        set {{3,0},{2,0},{2,1}},
        set {{3,-2},{2,-2},{2,-1}} } );

c = toricChernCharacter V;
assert(
  set apply(values c, l -> set entries transpose fold(l, (i,j) -> i|j)) ===
  set { set {{2,2},{3,0},{3,-2}},
        set {{-2,3},{1,3},{2,1}},
        set {{-2,2},{1,0},{2,-2}} } );

assert(isGloballyGenerated V);
assert(not isVeryAmple V);

assert(isNef V);
assert(isAmple V);
///


-- TODO : Redo this test 

-- Test 6
TEST ///
-- Test with a randomized vector bundle on 3-dim variety

r = 2 + random 4
F = toricProjectiveSpace 1 ** hirzebruchSurface r
E = randomDeformation tangentBundle F
while not isLocallyWeil E do (
 E = randomDeformation(tangentBundle F,4)
)

--applyValues(filtration E, entries)
--applyValues(base E, entries)

gs = groundSet E
p = parliament E;
par = unique entries transpose fold(flatten apply(values p, latticePoints), (i,j) -> i|j)

c = toricChernCharacter E

degs = unique degrees HH^0 E

assert( set par === set degs )
-*
cList  = apply(values c, l-> fold(l,(i,j)->i|j))
 wList = findWeights E

assert( #cList == #wList )

-- assumes that both lists have equal length
areEqualListsModPerm = (L1,L2) -> (
  if #L1 == 0 then return true; --implicit: #L2==0
  pos := positions(L2, l-> l==L1#0);
  if #pos == 0 then return false;
  return areEqualListsModPerm(drop(L1,{0,0}),drop(L2,{pos#0,pos#0}))
)

getColumns := mat -> toList apply( 0..<numgens source mat, i->mat_i )

foundList = for i in 0 ..< #cList list (
 found := -1;
 for j in 0 ..< #wList do (
  cChars := getColumns cList_i;
  for k in 0 ..< #(wList_j) do (
   wChars := getColumns (wList_j)_k;
   if areEqualListsModPerm(cChars,wChars) then (
    found = j;
    break;
   )
  )
 );
 found
)

assert(all(foundList, i->i>=0))
*-
///

-*

-- TODO : Redo this test

-- Test 7
TEST ///
-- Test with a randomized vector bundle of rank 3 on hirzebruch

r = 0 + random 5

X = hirzebruchSurface r

rk=3

while true do (
 FiltMat = for i to 3 list matrix {{random(QQ^rk,QQ^rk)}};
 if min apply(FiltMat, rank) == rk then break
)
FiltMat
FiltStep = for i to 3 list sort toList apply(0..<rk, i-> random(-5,5))
apply(FiltMat,entries)
apply(FiltStep,entries)

E = toricVectorBundle(X, FiltMat, FiltStep)

cB = compatibleBases E

tCC = toricChernCharacter E
--assert( class tCC === HashTable)

cList = apply(values tCC,  l-> fold(l,(i,j)->i|j))

wList = findWeights E

assert(#cList == #wList)

getColumns := mat -> toList apply( 0..<numgens source mat, i->mat_i )

-- assumes that both lists have equal length
areEqualListsModPerm = (L1,L2) -> (
  if #L1 == 0 then return true; --implicit: #L2==0
  pos := positions(L2, l-> l==L1#0);
  if #pos == 0 then return false;
  return areEqualListsModPerm(drop(L1,{0,0}),drop(L2,{pos#0,pos#0}))
)

foundList = for i in 0 ..< #cList list (
 found := -1;
 for j in 0 ..< #wList do (
  cChars := getColumns cList_i;
  for k in 0 ..< #(wList_j) do (
   wChars := getColumns (wList_j)_k;
   if areEqualListsModPerm(cChars,wChars) then (
    found = j;
    break;
   )
  )
 );
 found
)

assert(all(foundList, i->i>=0))

///




-- TODO : Redo this test

-- Test 8
TEST ///
-- Test with a randomized vector bundle of rank 4 on hirzebruch

r = 0 + random 3

X = hirzebruchSurface r

rk=4

while true do (
 FiltMat = for i to 3 list matrix {{random(ZZ^rk,ZZ^rk)}};
 if min apply(FiltMat, rank) == rk then break
)
FiltMat
FiltStep = for i to 3 list sort toList apply(0..<rk, i-> random(-5,5))
apply(FiltMat,entries)
apply(FiltStep,entries)

E = toricVectorBundle(rk, X, FiltMat, FiltStep)

cB = compatibleBases E

tCC = toricChernCharacter E

cList = apply(values tCC,  l-> fold(l,(i,j)->i|j))
wList = findWeights E

assert(#cList == #wList)

getColumns := mat -> toList apply( 0..<numgens source mat, i->mat_i )

-- assumes that both lists have equal length
areEqualListsModPerm = (L1,L2) -> (
  if #L1 == 0 then return true; --implicit: #L2==0
  pos := positions(L2, l-> l==L1#0);
  if #pos == 0 then return false;
  return areEqualListsModPerm(drop(L1,{0,0}),drop(L2,{pos#0,pos#0}))
)

foundList = for i in 0 ..< #cList list (
 found := -1;
 for j in 0 ..< #wList do (
  cChars := getColumns cList_i;
  for k in 0 ..< #(wList_j) do (
   wChars := getColumns (wList_j)_k;
   if areEqualListsModPerm(cChars,wChars) then (
    found = j;
    break;
   )
  )
 );
 found
)

assert(all(foundList, i->i>=0))
///

-- Test 9
TEST ///
-- Test whether the filtration steps obtained from the toric Chern character are correct
-- Such a test would have failed before version 1.8, 
-- because of a bug in the internal method flags:
-- the method made an assumption on the form how the filtration steps are ordered 
-- in the bundles generated by the package ToricVectorBundles. 
-- Usually true, this assumption does not apply, if the bundle arises 
-- by using the method dual of ToricVectorBundles (e.g. cotangent bundles).

X = toricProjectiveSpace 2
E = dual tangentBundle X

getCols = mat -> toList apply( 0..<numgens source mat, i->mat_i )

filtE = hashTable apply(rays E, rho -> rho =>filtrationJumps(E, rho));

filtFromTCC = applyPairs( toricChernCharacter E, (cone,us) -> 
 cone => (
  filtRay := for ray in getCols cone list sort apply(us, u -> ( (transpose matrix ray)*u)_(0,0))
 )
);

applyPairs(filtFromTCC, (cone, filts) -> (
  cone => for ray in getCols cone do
           assert isMember( sort filtE#(flatten transpose entries matrix ray), filts)
 )
)
///

*-

-- TODO: check if we still want the function and see how to test it


-*
-- Test 10
TEST ///
-- the methods dual, tensor (and maybe others?) from ToricVectorBundles
-- may produce a ToricVectorBundle whose matrices containing the filtration steps
-- have not ascending entries.
-- The method wellformedBundleFiltrations (added in version 1.9) ensures ascending entries.
-- The following test fails when omitting this method.
X = toricProjectiveSpace 2
T = tangentBundle X
E = wellformedBundleFiltrations( T ** (dual T))
F = wellformedBundleFiltrations((dual T) ** T)

origin = matrix map(ZZ^2,ZZ^1,0)

assert( all(values toricChernCharacter E, L -> isMember(origin, L)) )
assert( all(values toricChernCharacter F, L -> isMember(origin, L)) )
///
*-
end



---------------------------------------
-- END OF FILE
---------------------------------------
end

restart
debug needsPackage "ToricVectorBundles"
check "ToricVectorBundles"

X = toricProjectiveSpace 3
(filts, jumps) = toSequence transpose for i to 3 list {random(ZZ^3,ZZ^3),for j to 2 list random(-3,3)}
E = toricVectorBundle(X,filts,jumps)

-- We store some archived code that René wrote.

X = toricProjectiveSpace 1
--source
mats = {map(QQ^6,QQ^6,{{1, 0, 0, 0, 0, 0}, {0, 1, 0, 0, 0, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 0, 0}, {0, 0, 0, 0, 1, 0}, {0, 0, 0, 0, 0, 1}}),map(QQ^6,QQ^6,{{1, 0, 0, 0, 0, 0}, {0, 1, 0, 0, 0, 0}, {0, 0, 1, 0, 0, 0}, {0, 0, 0, 1, 0, 0}, {0, 0, 0, 0, 1, 0},
       {0, 0, 0, 0, 0, 1}})}
jumps = {{0,0,0,1,1,1},{0,0,1,0,0,1}}
E = toricVectorBundle(X,mats,jumps)
-- target
mats' = {map(QQ^2,QQ^2,{{1, 0}, {0, 1}}),map(QQ^2,QQ^2,{{1, 0}, {0, 1}})}
jumps' = {{2,2},{2,2}}
E' = toricVectorBundle(X,mats',jumps')
-- map
M = map(QQ^2,QQ^6,{{1, 0, 1, 1, 0, 1}, {0, 1, 0, 0, 1, 0}})
f = map(E',E,M)

-*
    -- This is a convenient step for what follows
    nrw := numrows newMatrices_0;
    --newMatrices = apply(# Xrays ,i ->matrix  submatrix' (rsort (newMatrices_i|| matrix{newJumps_i}), {nrw},));
    --newJumps = rsort newJumps;
    tvb := toricVectorBundle(X, newMatrices, newJumps);
    -- If the matrices are alredy square we dont need to modigy them
    if nrw =!= numcols newMatrices_0 then(
    rnew := rank newMatrices_0;
    -- note that a ToricVectorBundle can be defined with matrices that are not square and filteredPiece still works
    aux := flatten apply( steps, j -> apply(rays E2, rho ->filteredPiece(tvb, rho, j) ) );
    aux =  flatten apply(toList(1..rnew), i -> select(aux, M -> numcols M == i ) );
    -- When doing the fold the zero columns are automatically removed    
    Maux := fold((i,j) -> i|j, aux);
    baseCh:= linearMapFromMatrices(Maux,id_((ring E1)^rnew));
    phi := map(  twist( trivialBundle(X, rnew), apply(newJumps, i  ->  max i)), tvb, baseCh);
    1/0;
    tvb  = image phi;
    );
    *-