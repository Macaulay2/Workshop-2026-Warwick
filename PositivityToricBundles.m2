--*- coding: utf-8 -*-

------------------------------------------------------------------------------
-- PURPOSE : Check positivity of toric vector bundles
-- PROGRAMMER : Andreas Hochenegger
------------------------------------------------------------------------------

newPackage("PositivityToricBundles",
           Headline => "check positivity of toric vector bundles",
           Version => "1.9",
           Date => "August, 2024",
           Authors => { 
            {Name => "Andreas Hochenegger",
             Email => "andreas.hochenegger@polimi.it"}},
           Keywords => {"Toric Geometry"},
           Configuration =>{},
	   PackageImports => {},
           PackageExports => {"ToricVectorBundles"},
           DebuggingMode => true
          )

export {
        "groundSet", 
        "parliament",
        "compatibleBases",
        "isLocallyWeil",
        --"isLocallyFree",
        "cartierInd",
        "toricChernCharacter",
        "graphToricChernCharacter",
        "separatesJets",
        "isGloballyGenerated",
        "restrictToInvCurves",
        --"isNef",
        --"isAmple",
        "drawParliament2Dtikz",
        "wellformedBundleFiltrations",
-- Options
        "Verbosity",
        "DrawCohomology",
        "DrawChernCharacter"
        }

-- cacheValues
protect basesSortedByFiltrations 
protect filtrationFlags
protect posetTvb
protect restrictionsToInvCurves
protect isLW
protect isLF
-- Options
protect DrawCohomology
protect DrawChernCharacter
protect Verbosity
protect preferredGenerators

---------------------------------------------------------------------------
-- COPYRIGHT NOTICE:
--
-- Copyright 2024 Andreas Hochenegger
--
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


------------------------------------------------------------------------------
-- CAVEATS
------------------------------------------------------------------------------
-- 1) [K,RJS,P] uses decreasing filtration for Klyachko's description,
--    in contrast to the package 'ToricVectorBundles' (increasing filtration).
--    Source of confusion about different signs.
-- 2) We use same sign convention as in ToricVectorBundles, i.e.
--    given a polytope, the associated fan consists of inner normals
--    ([RJS,P] uses outer normals)
--    Another source of confusion about signs.
-- 3) We implicitly assume that the variety is at least complete and also smooth.
--    This is not tested, so  methods might break or results might become 
--    meaningless for varieties which are not complete or not smooth.
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- METHOD: groundSet
------------------------------------------------------------------------------
-- AUXILIARY METHODS FOR groundSet:
-- flags, getColumns, primitive, 
------------------------------------------------------------------------------

-- Old method in ToricVectorBundles
maxCones ToricVectorBundle := T -> (
      TV := fan T;
      TR := rays TV;
      TL := linealitySpace TV;
      mC := maxCones TV;
      apply(mC, c -> posHull(TR_c, TL))
    -- sort maxCones T#"ToricVariety"
   )


flags = method()
flags (ToricVectorBundle) := (cacheValue symbol filtrationFlags) ( E -> (
    fJs := unique flatten filtrationJumps( E);
    hashTable for rho in rays E list (
        rayFlag := unique for i in fJs list ((filteredPiece( E, rho, i)));
        rayFlag =  sort( select(rayFlag, M -> rank M != 0), mat -> numgens source mat);
        rho => rayFlag
    )
))

getColumns = method ()
getColumns (Matrix) := mat -> toList apply( 0..<numgens source mat, i->mat_i )
getColumns (Module) := M -> apply( getColumns gens M, c -> image matrix c)

primitive = method ()
primitive (Matrix) := mat -> (
 m := 1;
 if instance(mat_(0,0),QQ) then
  m = lcm apply(flatten entries mat, denominator);
 matmod := m*mat;
 m = gcd flatten entries matmod;
 lift(1/m*promote(matmod,QQ),ZZ)
)

-- is there a better way?

cartesianProduct2= (L1,L2) -> flatten apply(L1, l1 -> apply(L2, l2 -> {l1,l2}))

cartesianProductNested = L -> fold(L, cartesianProduct2)
inductiveFlatten = (L,i) -> if i<=0 then L else ( {L#0} | inductiveFlatten (L#1,i-1))
cartesianProduct (List ) := L -> (
 if #L==1 then return apply(L#0, l-> {l}); -- border case
 n := #L-2;
 apply( cartesianProductNested L, l -> inductiveFlatten(l,n))
)


poset = method()
poset (ToricVectorBundle) := (cacheValue symbol posetTvb)  (E -> (
    -- do all possible intersections (over ring of defintion of E)
    intersections := apply( cartesianProduct values flags E, L -> intersect( apply(L, l -> image promote(l,ring E) ) ) );
    -- remove 0-dimensional spaces and duplicates 
    intersections = toList set select( intersections, V -> rank V > 0 );
    intersections
))

-- MAIN METHOD: groundSet ----------------------------------------

-- PURPOSE : Given a toric vector bundle in Klyachko's description,
--           compute the ground set of the associated matroid
--           IMPORTANT: Due to the implementation, elements might appear several times
--   INPUT : 'tvb', a ToricVectorBundle
--  OUTPUT : ground set (list of nx1-matrices)
groundSet = method(Options => true)
groundSet (ToricVectorBundle) :=  {Verbosity => 0, preferredGenerators => {}} >> opts -> (cacheValue groundSet)  (E -> (
    if opts#Verbosity>0 then << "METHOD: groundSet" << endl;
    intersections := poset E;
    if opts#Verbosity>0 then << "Poset of proper linear subspaces of E: " << endl << apply(intersections,gens) << endl;
    R := ring E;
    G := toList set select( intersections, V -> rank V == 1 );
    if opts#Verbosity>0 then << "Initialize G with the one-dimensional subspaces: " << endl << apply(G,gens) << endl;
    for k in 2..rank E do (
        Vs := select( intersections, V -> rank V == k );
        if opts#Verbosity>0 then << "The " << k << "-dimensional subspaces: " << endl << apply(Vs,gens) << endl;
        for V in Vs do (
            GinV := select(G, g -> isSubset(g, V) );
            if opts#Verbosity>0 then << "V = " << gens V << " contains " << apply(GinV,gens) << endl;
            sumGinV := sum append(GinV, image map(R^(rank E),R^1,0)); -- works also if GinV empty
            if rank sumGinV < rank V then (
                newGs := {};
                generatorsToChoose := {};
                if #(opts#preferredGenerators) > 0 then (
                    generatorsToChoose = select( apply(opts#preferredGenerators, g -> image promote(g,R)), g -> isSubset(g, V));
                    )
                else (
                    generatorsToChoose = toList getColumns V;
                    );
                if opts#Verbosity>0 then << "generators in V: " << apply(generatorsToChoose, gens) << endl;
                generatorsToChoose = select( generatorsToChoose, v -> not isSubset(v, sumGinV));
                if opts#Verbosity>0 then << "generators not in " << apply(GinV,gens) << ": " << apply(generatorsToChoose, gens) << endl;
                while rank(sumGinV + sum append(newGs, image map(R^(rank E),R^1,0))) < rank V do (
                    if rank(sumGinV+sum append(newGs, image map(R^(rank E),R^1,0))+generatorsToChoose#0) > rank(sumGinV+sum append(newGs, image map(R^(rank E),R^1,0))) then (
                        if opts#Verbosity>0 then << "add generator: " << gens generatorsToChoose#0 << endl;
                        newGs = append(newGs, generatorsToChoose#0);
                    );
                    generatorsToChoose = drop(generatorsToChoose,1);
                );
                G = G | newGs;
                if opts#Verbosity>0 then << "Updated G to " << apply(G,gens) << endl;
            )
            else (
                if opts#Verbosity>0 then << "is already generated by G." << endl;
            )
        )
    );
-- return to ZZ
    apply(toList set G, g -> primitive gens g)
))

------------------------------------------------------------------------------
-- METHOD: parliament
------------------------------------------------------------------------------
-- AUXILIARY METHODS FOR parliament:
-- polytopeTVB
------------------------------------------------------------------------------

polytopeTVB = method(Options => true)
polytopeTVB (ToricVectorBundle, Matrix) := {Verbosity => 0} >> opts -> ( (E,l) -> (
    if opts#Verbosity>0 then << "Calculate polytope for l = " << l << endl;
    rayE := rays E;
    filtSteps := hashTable for rho in rayE list (
        rho => sort unique flatten (-filtrationJumps (E, rho))
    );
    flgs:= flags E;
    R := ring E;
    M := transpose matrix { apply( rayE, rho -> (filtSteps#rho)#(position((flgs)#rho, f -> isSubset(image promote(l,R), image promote(f,R))))) };
    rhoMat := transpose fold((i,j) -> i|j,  apply(rayE , i -> transpose matrix {i}) );
    if opts#Verbosity>0 then << "the equations for the polytope are:" << endl <<  rhoMat << "*x >= " << M << endl;
    M = promote(M,R);
    rhoMat = promote(rhoMat,R);
    pol := polyhedronFromHData(-rhoMat,-M);
    if opts#Verbosity>0 then << "the associated polytope has vertices:" << endl << vertices pol << endl;
    pol
    
))



-- Main method: parliament ---------------------------------------------------

-- PURPOSE : Given a toric vector bundle in Klyachko's description
--           and the ground set of the associated matroid,
--           compute the parliament of polytopes [RJS]
--   INPUT : 'tvb', a ToricVectorBundle
--  OUTPUT : parliament of polytopes, hash table (ground set => parliament)
parliament = method()
parliament(ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue parliament)( E -> (
    if opts#Verbosity>0 then << "METHOD: parliament" << endl;
    gs := groundSet(E, Verbosity=>(opts#Verbosity-1));
    hashTable for l in gs list ( l => polytopeTVB(E,l, Verbosity=>opts#Verbosity) )
))

------------------------------------------------------------------------------
-- METHOD: compatibleBases
------------------------------------------------------------------------------
-- AUXILIARY METHODS FOR compatibleBases:
-- restrictToAffine, compatibleBasis
------------------------------------------------------------------------------


restrictToAffine = method(Options => true)
restrictToAffine (ToricVectorBundle, Cone) := {Verbosity => 0} >> opts -> ( (tvb,cone) -> (
    if opts#Verbosity>0 then << "METHOD: restrictToAffine" << endl;
    TV := normalToricVariety(fan cone, CoefficientRing => ring tvb );
    rayC := rays TV;
    toricVectorBundle(TV, apply( rayC, rho -> filtrationMatrices(tvb, rho)), apply(rayC, rho -> filtrationJumps(tvb, rho)) )
))

restrictToAffine (ToricVectorBundle, Matrix) := {Verbosity => 0} >> opts -> ( (tvb,cone) -> (
    if opts#Verbosity>0 then << "METHOD: restrictToAffine" << endl;
    TV := normalToricVariety(fan coneFromVData cone, CoefficientRing => ring tvb );
    rayC := rays TV;
    toricVectorBundle(TV, apply( rayC, rho -> filtrationMatrices(tvb, rho)), apply(rayC, rho -> filtrationJumps(tvb, rho)) )
))

-- PURPOSE: Given the possible flags (as computed by possibleFlags) for rays of maximal cone
--          compute a common set of basis vectors
--   INPUT: 'tvb', toric vector bundle
--          'sigma', maximal cone
--  OUTPUT: compatible base (matrix of vectors)

compatibleBasis = method(Options => true)
compatibleBasis (ToricVectorBundle, Cone) := {Verbosity => 0} >> opts -> (E,C) -> (
    
 if opts#Verbosity>0 then << "METHOD: compatibleBasis" << endl;
    F:= restrictToAffine(E, C, Verbosity=>opts#Verbosity);
     if opts#Verbosity>0 then << "details of bundle restricted to " << C << endl << details E << endl;
    fold(groundSet (F, Verbosity=>opts#Verbosity-1, preferredGenerators=> groundSet E), (i,j) -> i|j)
    
)

compatibleBasis (ToricVectorBundle, Matrix) := {Verbosity => 0} >> opts -> (E,C) -> (
    
 if opts#Verbosity>0 then << "METHOD: compatibleBasis" << endl;
    F:= restrictToAffine(E, C, Verbosity=>opts#Verbosity);
     if opts#Verbosity>0 then << "details of bundle restricted to " << C << endl << details E << endl;
    fold(groundSet (F, Verbosity=>opts#Verbosity-1, preferredGenerators=> groundSet E), (i,j) -> i|j)
    
)

-- MAIN METHOD: compatibleBases ----------------------------------------------

-- PURPOSE: Given a toric vector bundle in Klyachko's description
--          compute list of compatible bases as in [RJS, Section 3]
--   INPUT: 'tvb', toric vector bundle
--  OUTPUT: hash table: max cone => compatible basis
compatibleBases = method( Options => true )
compatibleBases (ToricVectorBundle):= {Verbosity => 0} >> opts -> (cacheValue symbol compatibleBases) (E -> (
    
 if opts#Verbosity>0 then << "METHOD: compatibleBases" << endl;
    maxcones :=  maxCones E;
    --maxcones :=  apply(maxCones E,rays);
    hashTable for sigma in maxcones list (rays sigma => compatibleBasis (E , sigma, Verbosity=>opts#Verbosity ))
))

------------------------------------------------------------------------------
-- isLocallyWeil
------------------------------------------------------------------------------

-- PURPOSE: Given a toric reflexive sheaf in Klyachko's description
--          check whether it is locally Weil, that is, locally a direct sum of reflexive sheaves of rank 1
--   INPUT: 'tvb', toric vector bundle
--  OUTPUT: true or false

isLocallyWeil = method(Options => true)
isLocallyWeil (ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue isLW) (tvb -> (
    if opts#Verbosity>0 then << "METHOD: isLocallyWeil" << endl;
 cbs := compatibleBases (tvb, Verbosity=>opts#Verbosity);
 isVB := applyValues(cbs, b -> numgens source b == rank tvb);
  if opts#Verbosity>0 then (
   << "cones where sheaf is not locally Weil:" << endl;
   for cb in pairs cbs do if not cb#1 then << cb#0 << endl;
 );
 all(values isVB, i->i)
))

------------------------------------------------------------------------------
-- toricChernCharacter
------------------------------------------------------------------------------

-- PURPOSE : Given a toric vector bundle in Klyachko's description and
--           given compatible bases as computed by compatibleBases,
--           compute the toric Chern character as introduced in [Payne] 
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT : hash table: max cone => points of toric Chern character.

toricChernCharacter = method(Options => true)
toricChernCharacter (ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue toricChernCharacter) ( tvb -> (
 R := ring tvb;
 compBases := compatibleBases(tvb); 
 if opts#Verbosity>0 then << "METHOD: toricChernCharacter" << endl;
 filtSteps := hashTable for rho in rays tvb list (
  rho => sort unique flatten (-1* filtrationJumps (tvb,rho))
 );
 cI := 1; -- cartierIndex
 result := hashTable for cb in pairs compBases list (
maxcone := apply( 0..<numgens source cb_0, i-> entries (cb_0)_i );
 if opts#Verbosity>0 then << "For maximal cone sigma: " << endl << maxcone << endl;
base := apply( 0..<numgens source cb_1, i->matrix (cb_1)_i );
  if opts#Verbosity>0 then << "the compatible basis is: " << endl << base << endl;
cb_0 => for b in base list (
   RHS := for rho in maxcone list (
    i := position((flags tvb)#rho, f -> isSubset(image promote(b,R), image promote(f,R)));
    filtSteps#rho#i
   );
   sol := solve(transpose promote(cb_0,R), transpose promote(matrix {RHS},R));
   if opts#Verbosity>0 then << "Solve equation: " << endl << transpose cb_0 << " *x= " << transpose matrix {RHS} << endl << "Solution: " << sol << endl;
   cI = lcm(cI, lcm( apply(flatten entries sol, denominator) ) );
   --if all(flatten entries sol, e -> liftable(e,ZZ)) then
   -- sol = lift(sol,ZZ); 
   sol
  )
 );
 tvb.cache.cartierInd = cI;
 if cI == 1 then (
  tvb.cache.isLF = true;
  result = applyValues(result, c -> apply(c, m -> lift(m,ZZ)));
 )
 else (
  tvb.cache.isLF = false;
  if opts#Verbosity>0 then << "Cartier index is: " << cI << endl;
 );
 result
))
 
isLocallyFree ToricVectorBundle :=  tvb -> (
 if not isLocallyWeil tvb then (return false;);
 if not tvb.cache.?isLF then (toricChernCharacter tvb);
 tvb.cache.isLF
)

cartierInd = method()
cartierInd (ToricVectorBundle) := tvb -> (
 if not tvb.cache.?cartierInd then
  toricChernCharacter tvb;
 tvb.cache.cartierInd
)


-- PURPOSE : Given a toric vector bundle in Klyachko's description and
--           its toric Chern character,
--           connect components in adjacent maximal cones by lines
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT : hash table: cone of codim 1 (curve) => list of pairs
graphToricChernCharacter = method(Options => true)
graphToricChernCharacter (ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue graphToricChernCharacter) ( tvb -> (
 torChern := toricChernCharacter(tvb);
 if opts#Verbosity>0 then  << "METHOD: graphToricChernCharacter" << endl;
 F := fan tvb;
 n := dim F;
 raysF := rays F;
 curveCones := apply(cones(n-1,F), c -> (raysF)_c);
 hashTable for tau in curveCones list (
    if opts#Verbosity>0 then  << "For curve cone: " << endl << tau << endl;
  sigmas := {};
  normal := kernel transpose tau;
  if opts#Verbosity>0 then  << "has normal: " << endl << normal << endl;
  for sigma in keys torChern do
   if contains(coneFromVData sigma, coneFromVData tau) then
     sigmas = append(sigmas,sigma);
    if opts#Verbosity>0 then  << "the adjacent maximal cones are: " << endl << sigmas << endl;
  edges := {};
  for u1 in torChern#(sigmas_0) do ( 
   for u2 in torChern#(sigmas_1) do (
    if isSubset(image(u1-u2), normal) then (
    if opts#Verbosity>0 then  << "connect Chern components: " << endl << {u1,u2} << endl;
     edges = append(edges, {u1,u2});
    ); 
   );
  );
  tau => edges
 )
))




------------------------------------------------------------------------------
-- METHOD: separateJets
------------------------------------------------------------------------------

separatesJetsLocally = method( Options => true )
separatesJetsLocally (ToricVectorBundle,Cone) := {Verbosity => 0} >> opts -> (tvb,sigma) -> (
    if opts#Verbosity>0 then << "METHOD: separatesJetsLocally" << endl;
 sigmaMat := rays sigma;
  if opts#Verbosity>0 then << "for the maximal cone sigma " << sigmaMat << endl;
 R := ring tvb;
 uSigma := apply((toricChernCharacter tvb)#sigmaMat, c -> promote(c,R));
 uSigmaSet := toList set uSigma;
 uSigmaMult := apply(uSigmaSet, u -> number(uSigma, w -> u==w));
  if opts#Verbosity>0 then << "the u(sigma) are " << uSigmaSet <<  " with multiplicities " << uSigmaMult << endl;
 par := parliament tvb;
 parVertices := applyValues(par, pol -> apply(getColumns vertices pol, c -> matrix promote(c,QQ)) );
 if opts#Verbosity>0 then << "the parliament is " << parVertices << endl;
-- [RJS, Thm 6.2, condition (i)]
 uSigmaAreVertices := hashTable apply(uSigmaSet, u -> u => applyValues(parVertices, pol -> member(u, pol)));
 uSigmaAreVerticesNumber := applyValues( applyValues(uSigmaAreVertices, values), trueFalse -> number(trueFalse, i->i==true));
 -- check whether all uSigma are vertices of as many polytopes as their multiplicity
 if not all(0 ..< #uSigmaSet, i-> uSigmaAreVerticesNumber#(uSigmaSet#i) >= uSigmaMult#i ) then 
 (
  return -infinity;
 );
-- [RJS, Thm 6.2, condition (ii+iii)]
 sigmaDual := dualCone sigma;
 -- gives u=> {e's} such that u vertex of P(e) and u+sigma^vee contains P(e)
 --uSigmaPE := applyPairs(uSigmaAreVertices, (u,eAV) -> (u, keys selectPairs(eAV, (e,AV) -> AV and contains(convexHull u + sigmaDual, par#e) ) ));
 uSigmaPE := applyPairs(uSigmaAreVertices, (u,eAV) -> (u, keys hashTable select(pairs eAV, (e,AV) -> AV and contains(convexHull u + sigmaDual, par#e) ) ));
 uSigmaPEnumber := applyValues(uSigmaPE, Ps -> #Ps);
 -- [RJS, Thm 6.2, condition (iv)]
 if min values uSigmaPEnumber == 0 then (
    if opts#Verbosity>0 then << "there is no polytope with suitable local structure for at least one u(sigma): " << applyValues(uSigmaPE, l -> apply(l, e -> parVertices#e)) << endl;
    if opts#Verbosity>0 then << << "on sigma not globally generated." << endl;
 
  return -infinity;
 );
 if opts#Verbosity>0 then << "the u(sigma) appear as vertices (and with locally correct structure) of " << applyValues(uSigmaPE, l -> apply(l, e -> parVertices#e)) << endl;
 oneFaces := facesAsCones(dim (variety tvb) -1, sigmaDual);
 -- calculate the intersection of the edges of u+sigmaDual with P(e)
 edges := applyPairs(uSigmaPE, (u,es) -> (u, apply(es, e->  apply(oneFaces, f-> intersection(convexHull u + f, par#e)))));
 -- transform result into matrices whose columns are the vertices of the edges
 edges = applyValues(edges, edgeSet -> apply(edgeSet, polSet -> apply(polSet, pol -> matrix vertices pol )));
 if opts#Verbosity>0 then << "the intersections of u+sigmaDual with P(e) have vertices " << edges << endl;
 -- calculate the lattice length and take for each P(e) the minimal one
 edgeLengths := applyValues(edges, edgeSet -> apply(edgeSet, matSet -> min apply(matSet, mat -> gcd flatten entries (mat_0 - mat_(numgens source mat-1)))));
 -- [RJS, Thm 6.2, condition (iv)]
 -- check which combinations of P(e)s give a basis
 checkBaseOfMatroid := apply(cartesianProduct values uSigmaPE, es -> rank fold(es, (i,j)->i|j) == rank tvb);
 -- for all bases compute the minimal edge number, take maximum among all
 l := max apply(select(pack(2, mingle(checkBaseOfMatroid , cartesianProduct values edgeLengths)), i -> i#0), i -> min i#1);
  if opts#Verbosity>0 then (
  if l >= 0 then ( << "separates " << l << "-jets"  << endl ) else ( << "on sigma not globally generated." << endl )
 );
 l
)


-- PURPOSE : Given a toric vector bundle in Klyachko's description,
--           its parliament bases and toric Chern character
--           compute the maximal l such that the bundle separates l-jets
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT :  Integer, -infinity if not separates any l-jets, otherwise l
separatesJets = method(Options => true)
separatesJets (ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue separatesJets) ( tvb -> (
 if opts#Verbosity>0 then << "METHOD: separatesJets" << endl;
 min( apply( maxCones tvb, sigma -> separatesJetsLocally(tvb,sigma, Verbosity=>opts#Verbosity) ) )
))

------------------------------------------------------------------------------
-- METHODS: isGloballyGenerated, isVeryAmple
------------------------------------------------------------------------------


-- PURPOSE : Given a toric vector bundle in Klyachko's description,
--           its parliament, compatible bases and toric Chern character
--           check if the vector bundle is globally generated, using [RJS, Thm. 1.2]
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT :  'true' if globally generated, otherwise 'false'
isGloballyGenerated = method( Options => true )
isGloballyGenerated (ToricVectorBundle) := {Verbosity => 0} >> opts -> (tvb) -> 
if separatesJets(tvb, Verbosity=>opts#Verbosity) >= 0 then true else false;


-- PURPOSE : Given a toric vector bundle in Klyachko's description,
--           its parliament, compatible bases and toric Chern character
--           check if the vector bundle is very ample, using [RJS, Cor. 6.7]
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT :  'true' if very ample, otherwise 'false'
--isVeryAmple = method( Options => true ) -- already defined in Polyhedra
isVeryAmple (ToricVectorBundle) := {Verbosity => 0} >> opts -> tvb -> separatesJets(tvb, opts) >= 1
  
------------------------------------------------------------------------------
-- METHOD: restrictToInvCurves, isNef, isAmple
------------------------------------------------------------------------------
-- AUXILIARY METHODS FOR isNef, isAmple:
-- restrictToCurve
------------------------------------------------------------------------------

-- PURPOSE : Given a toric vector bundle in Klyachko's description,
--           a cone corresponding to a curve of the toric variety and
--           its toric Chern character,
--           compute the restriction of the vector bundle to the curve.
--   INPUT :
--           'tau', (n-1)-dim cone given as matrix of rays
--           'torChern', toric Chern character
--  OUTPUT : list of integers (a_i) such that E|_C = \sum O_C(a_i)
restrictToCurve = method( Options => true)
restrictToCurve (Matrix,HashTable) := {Verbosity => 0} >> opts -> (tau,torChern) -> (
 normal := generators kernel transpose tau;
 if opts#Verbosity>0 then << "a vector normal to tau:" << endl << normal << endl;
 sigmas := {};
 for sigma in keys torChern do (
  if contains(coneFromVData sigma, coneFromVData tau) then (
   proj := flatten entries (transpose normal * sigma);
   if all(proj, n -> n >= 0) then
    sigmas = prepend(sigma,sigmas)
   else
    sigmas = append(sigmas,sigma);
  );
 );
 if opts#Verbosity>0 then << "the adjacent maximal cones sigma1 and sigma2 are:" << endl << sigmas << endl;
 for u0 in torChern#(sigmas_0) list (
  local a;
  for u1 in torChern#(sigmas_1) do (
   -- opposite due to different sign convention in [RJS]
   diff := u1-u0;
   as := unique select(apply(entries(diff|normal), i -> if i_1==0 then (if not i_0==0 then infinity) else i_0/i_1), x -> instance(x,Number) or instance(x,InfiniteNumber));
   if #as == 1 then (
    a = as_0;
    if opts#Verbosity>0 then << "the Chern components u1 and u2 lie on a line orthogonal to tau: " << endl << {u0,u1} << endl 
                           << "their difference is " << a << " times the normal." << endl;
    break;
   );
  );
  a
 )
)

-- MAIN METHODS: restrictToInvCurves, isNef, isAmple -----------------------------

restrictToInvCurves = method(Options => true)
restrictToInvCurves (ToricVectorBundle) := {Verbosity => 0} >> opts -> (cacheValue symbol restrictionsToInvCurves) ( tvb -> (
 torChern := toricChernCharacter( tvb);
 if opts#Verbosity>0 then << "METHOD: restrictToInvCurves" << endl;
 F := fan tvb;
 n := dim fan tvb;
 curveCones := apply(cones(n-1,F), c -> (rays F)_c);

 hashTable for tau in curveCones list (
    if opts#Verbosity>0 then << "Restriction to codim1 cone tau:" << endl << tau << endl;
  tau => restrictToCurve(tau,torChern)
 )
))


-- PURPOSE : Given a toric vector bundle in Klyachko's description and
--           its toric Chern character,
--           compute whether the bundle is nef or ample, using [HMP, Thm. 2.1]
--   INPUT : 'tvb', toric vector bundle
--  OUTPUT : hash table
--isNef = method( Options => true)
isNef (ToricVectorBundle) := {Verbosity => 0} >> opts -> tvb -> (
     if opts#Verbosity>0 then << "METHOD: isNef" << endl;
 restrictions := restrictToInvCurves(tvb, Verbosity => opts#Verbosity);
 all(values restrictions, r -> all(r, x -> x >=0))
)

--isAmple = method( Options => true)
isAmple (ToricVectorBundle) := {Verbosity => 0} >> opts -> tvb -> (
 if opts#Verbosity>0 then << "METHOD: isAmple" << endl;
 restrictions := restrictToInvCurves(tvb, Verbosity => opts#Verbosity);
 all(values restrictions, r -> all(r, x -> x >0))
)

------------------------------------------------------------------------------
-- METHOD: drawParliament2Dtikz
------------------------------------------------------------------------------
-- AUXILIARY METHODS FOR drawParliament2Dtikz:
-- sortByAngle, circularOrder
------------------------------------------------------------------------------

-- PURPOSE : Given a list of points in the plane, 
--           and a list of the angles (interpret points as complex numbers),
--           sort the points by angle
sortByAngle = method()
sortByAngle (List,List) := (p, angles) -> (
 if #p == 1 then return p;
 for i from 0 to #p-2 do 
  if angles_(i+1) < angles_i then
   return sortByAngle(switch(i,i+1,p),switch(i,i+1,angles));
 p
)

-- PURPOSE : Given a list of points in the plane,
--           sort them in circular way around center of gravity
circularOrder = method()
circularOrder (List) := p -> (
 mid := sum p/#p;
 pmoved := apply(p, pt->pt-mid);
 angles := apply(pmoved, pt -> atan2(pt_1,pt_0));
 sortByAngle(p,angles)
)

-- MAIN METHOD: drawParliament2Dtikz -----------------------------------------

-- PURPOSE: Draw a two-dimensional parliament of polytopes using tikz
--   INPUT: 'tvb', toric vector bundle,
--          'file', string with file name
--  OUTPUT: nothing to M2, output goes to file

drawParliament2Dtikz = method(Options => true)
drawParliament2Dtikz (ToricVectorBundle,String) := {DrawCohomology => true, DrawChernCharacter => true } >> opts -> (tvb,file) -> (
-- check for dimension 2
if dim fan tvb != 2 then (
 error "Error: only works for 2-dim parliaments.";
 return;
);

polys := apply(values parliament tvb, vertices);

offset := 0.3;
-- want (0,0) to be inside picture
maxx := max append(apply(polys, p->max flatten entries p^{0}),0);
maxy := max append(apply(polys, p->max flatten entries p^{1}),0);
minx := min append(apply(polys, p->min flatten entries p^{0}),0);
miny := min append(apply(polys, p->min flatten entries p^{1}),0);

-- <<"" is taken from documentation about
-- creating and writing files in M2
f := file << "";

f << ///\begin{tikzpicture}[scale=0.5]/// << endl;

if not minx == infinity then (
f << /// \draw[thin, color=black!75]/// << endl;
f << "  ("  << minx-offset << "," << miny-offset << ") grid (" << maxx+offset << "," << maxy+offset << ");" << endl << endl;
);

for pMat in polys do (
 -- check for empty polytope
 if source pMat==0 then continue;

 pts := circularOrder entries transpose pMat;
 f << /// \fill[color=black,opacity=0.1]/// << endl << "  ";
 for p in pts do (
  f << "(" << p_0 << "," << p_1 << ") -- ";
 );
 f << "cycle;" << endl;

 f << /// \draw[color=black,opacity=0.5]/// << endl << "  ";
 for p in pts do (
  f << "(" << p_0 << "," << p_1 << ") -- ";
 );
 f << "cycle;" << endl;
);


if opts#DrawCohomology then (
 H := apply(0 .. 2, i->degrees HH^i tvb);
 
 for h in H_0 do (
  f << /// \fill[color=blue,opacity=0.3]/// << endl;
  f << "  (" << h_0 << "," << h_1 << ") circle (2pt);" << endl;
 );
 
 for h in H_1 do (
  f << /// \fill[color=red,opacity=0.3]/// << endl;
  f << "  (" << h_0 << "," << h_1 << ") circle (2pt);" << endl;
 );
 
 for h in H_2 do (
  f << /// \fill[color=green,opacity=0.3]/// << endl;
  f << "  (" << h_0 << "," << h_1 << ") circle (2pt);" << endl;
 );
);

if opts#DrawChernCharacter then (
 chern := values toricChernCharacter tvb;
 for cs in chern do 
  for c in cs do (
   f << /// \draw[thick, color=yellow!50]/// << endl;
   f << "  (" << c_(0,0) << "," << c_(1,0) << ") circle (2pt);" << endl;
  );
 graphChern := graphToricChernCharacter tvb;
 for ray in keys graphChern do
  for u in graphChern#ray do (
   f << /// \draw[thin, color=yellow!50]/// << endl;
   f << "  (" << u_0_(0,0) << "," <<  u_0_(1,0) << ") -- (" << u_1_(0,0) << "," << u_1_(1,0) <<");" << endl;
  );
);

f << /// \draw[thick, color=black!50]/// << endl;
f << "  (0,0) circle (3pt);" << endl;

f << ///\end{tikzpicture}/// << endl;

f << close;
)


--- METHOD: wellformedBundleFiltrations -----------------------------------

-- PURPOSE: ensures ascending entries in the filtration matrices of a toric vector bundle
--   INPUT: 'tvb', toric vector bundle
--  OUTPUT: a toric vector bundle, whose filtration matrices have ascending entries

wellformedBundleFiltrations = method ()
-*
wellformedBundleFiltrations (ToricVectorBundle) := tvb -> (
 fMTlist := applyValues(filtration tvb, f -> sort flatten entries f );
 fMT := applyValues(fMTlist, f -> matrix {f});
 fMTunique := applyValues(fMTlist, unique);
 permutations := applyPairs(fMTunique, (rho,f)-> rho => apply(f, i-> positions(flatten entries (filtration tvb)#rho, j->i==j)) );
 bT := applyPairs(base tvb, (rho,m) -> rho => fold(apply(permutations#rho, i -> m_i), (i,j) -> i|j));
 -- the following is taken from ToricVectorBundles#makeVBKlyachko
 fT := hashTable apply(pairs fMT, p -> (
               L := flatten entries p#1;
               L1 := sort unique L;
               p#0 => hashTable ({(min L1-1) => {}} | apply(L1, l -> l => positions(L,e -> e == l)))));
 new ToricVectorBundle from {
               "ring" => tvb#"ring",
               "rayTable" => tvb#"rayTable",
               "baseTable" => bT,
               "filtrationMatricesTable" => fMT,
               "filtrationTable" => fT,
               "ToricVariety" => tvb#"ToricVariety",
               "number of affine charts" => tvb#"number of affine charts",
               "dimension of the variety" => tvb#"dimension of the variety",
               "rank of the vector bundle" => tvb#"rank of the vector bundle",
               "number of rays" => tvb#"number of rays",
               symbol cache => new CacheTable}
)
*-
 -- TODO decide if this method is still needed
wellformedBundleFiltrations (ToricVectorBundle) := tvb -> (
 fMTlist := hashTable apply( rays tvb, rho -> rho => -1*filtrationJumps(tvb, rho));
 fMT := applyValues(fMTlist, f -> matrix {f});
 fMTunique := applyValues(fMTlist, unique);
 permutations := applyPairs(fMTunique, (rho,f)-> rho => apply(f, i-> positions( -1*filtrationJumps(tvb, rho), j->i==j)) );
 basetvb :=  hashTable apply( rays tvb, rho -> rho => filtrationMatrices(tvb, rho));
 bT := applyPairs(basetvb, (rho,m) -> rho => fold( (i,j) -> i|j, apply(permutations#rho, i -> m_i)));
 -- the following is taken from ToricVectorBundles#makeVBKlyachko
 fT := hashTable apply(pairs fMT, p -> (
               L := flatten entries p#1;
               L1 := sort unique L;
               p#0 => hashTable ({(min L1-1) => {}} | apply(L1, l -> l => positions(L,e -> e == l)))));
 -- New data
 mats:= apply(rays tvb, rho -> bT#rho );
 jumps:= apply( rays tvb, rho -> -1*( flatten entries fMT#rho));
 toricVectorBundle( variety tvb, mats, jumps)
)

end

