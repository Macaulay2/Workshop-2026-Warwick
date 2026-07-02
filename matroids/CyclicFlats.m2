newPackage("CyclicFlats",
	AuxiliaryFiles => true,
	Version => "1.0.0",
	Date => "June 2026",
	Authors => {{
		Name => "",
		Email => ""}},
	Headline => "computations with cyclic flats",
	Keywords => {"Matroids"},
	HomePage => "",
        DebuggingMode => true
)
export {
	"CyclicFlats",
	"cyclicFlats",
        "BaseRing",
        "groundSet",
        "rankSum",
        "cyclicFlatsType",
        "cyclicFlatsAxioms",
        "evalValInvariant",
        "cFlats",
        "recFlats",
        "tutte",
        "tutteRing",
        "tutteUniform",
        "tutteCuspidal",
        "tutteUnisum"
}

needsPackage "Posets"


CyclicFlats = new Type of HashTable;
CyclicFlats.synonym = "cyclicFlats";


globalAssignment CyclicFlats
net CyclicFlats := M -> (
    net ofClass class M | " of rank " | toString(M.rank) | " on " | toString(#M.groundSet) | " elements"
    )

cyclicFlats = method()
cyclicFlats(HashTable) := H -> (
    cyclicFlatsType := cFlats -> (
        scanPairs(cFlats, (Flat, Rank) -> (
                if not (instance(Flat, Set) or instance(Flat, List) or instance(Flat, Sequence)) then (
                    if debugLevel > 0 then printerr("Error: " | toString(Flat) | " is not iterable.");
                    error "Invalid flat.";
                    );

                if not instance(Rank, ZZ) then (
                    if debugLevel > 0 then printerr("Error: " | toString(Rank) | " is not an integer.");
                    error "Invalid rank.";
                    );
                )
            );
        true
        );
    if not cyclicFlatsType H then error "Incorrect type for CyclicFlats matroid.";
    H2 := new HashTable from applyPairs(H, (k, v) -> (
            set k => v
            ));
    cyclicFlatsAxioms := cFlats -> (
        G := keys cFlats;
        P := poset(G, isSubset);
        --Z0
        if not isLattice P then (
            if debugLevel > 0 then printerr("Error: " | toString(P) | " is not a poset under inclusion.");
            return false;
            );
        --Z1
        if not (( isMember(set {}, G)) and  (cFlats#(set{}) == 0)) then (
            if debugLevel > 0 then printerr("Error: " | toString(cFlats) | "does not satisfy axiom Z1."); -- TODO: Make error message more specific.
            return false;
        );
 
        --Z2
        for g in G do (
            for h in principalFilter(P,g) do (
                if (g != h) then(  --maybe figure out a way around this, like just removing g from the principal filter
                    if cFlats#h - cFlats#g == 0 or cFlats#h - cFlats#g >= #(h - g) then (
                        if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom."); -- TODO: Make error message more specific.
                        return false;
                        );
                    )
                )
            );
        --Z3
        for g in G do (
            for h in G do (
                rankSum := cFlats#g + cFlats#h;
                pJoin := first posetJoin(P, g, h);
                pMeet := first posetMeet(P, g, h);
                rankJoin := cFlats#(pJoin);
                rankMeet := cFlats#(pMeet);
                if ( rankSum < rankJoin + rankMeet + #(intersect(g,h)) - #(pMeet)) then (
                    if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom."); -- TODO: Make error message more specific.
                    return false;
                    );
                );
            );
        true
        );
    if not cyclicFlatsAxioms H2 then error "Given hashtable " | toString H | " does not satisfy the axioms of a collection of cyclic flats.";
    M := new CyclicFlats from {
        symbol groundSet => union keys H2,
        symbol rank => max values H2,
        symbol cyclicFlats => H2
        };
    M
    );

countStressedSubsets = method();
countStressedSubsets(CyclicFlats, ZZ, ZZ) := (M, r, h) -> (
    num := 0;
    scanPairs(M.cyclicFlats, (S, ri) -> if ri == r and #S == h then num += 1);
    num
    );

evalValInvariant = method( Options => {BaseRing => tutteRing});
evalValInvariant (CyclicFlats, MethodFunctionWithOptions, MethodFunctionWithOptions, MethodFunctionWithOptions) := opts -> (M, Uniform, Cuspidal, Unisum) -> (
    -*
    Inputs:
        M: CyclicFlats matroid object.
        Other params are evaluations of the valuative invariant on specific types of matroids indexed by tuples of integers:
        Uniform: (k, n): Uniform matroid U_{k, n}
        Cuspidal: (r, k, h, n): Cuspidal matroid L_{r, k, h, n}
        Unisum: (r, k, h, n): Sum of uniform matroids U_{r, h} + U_{k-r, n-h}
    *-
    k := M.rank;
    n := #(M.groundSet);
    total := Uniform(k, n); 
    summy := sum apply(toList(1..k), r -> (
                sum apply(toList(r..n), h -> ( --Requires toList because sum needs a list and r..n naturally returns a Sequence
                        
                        lam := countStressedSubsets(M, r, h);
                        lam * (Cuspidal(r, k, h, n) - Unisum(r, k, h, n))
                        )
                    )
                )
            ); 
    return total - summy
);


tutteRing := ZZ(monoid(["x","y"]/getSymbol));
tutteUniform = method(Options => {BaseRing => tutteRing});
tutteUniform (ZZ, ZZ) := RingElement => opts -> (k, n) -> (
    R := opts.BaseRing;
    total := sum apply(k, i -> binomial(n-i-2, n-k-1)*R_0^(i+1));
    total += sum apply(n-k, i -> binomial(n-i-2, k-1)*R_1^(i+1));
    total
    );

-- From Proposition 7.18
tutteCuspidal = method(Options => {BaseRing => tutteRing});
tutteCuspidal (ZZ, ZZ, ZZ, ZZ) := RingElement => opts -> (r, k, h, n) -> (
    R := opts.BaseRing;

    alpha := (i, j, r, k) -> (
        if (i + j <= k) 
        then (R_0 - 1)^(k-i-j)*(1-((R_0-1)*(R_1-1))^(i-r)) 
        else (R_1 - 1)^(i+j-k)*(1-((R_0-1)*(R_1-1))^(k-r-j))
        );
    
    total := tutteUniform(k-r, n-h, BaseRing => R) * tutteUniform(r, h, BaseRing => R);
    total += sum apply(toList(r+1..h), i -> (
            sum apply(toList(0..k-r-1), j -> (
                    binomial(h, i) * binomial(n-h, j) * alpha(i, j, r, k)
                    )
                )
            )
        );
    total
    );
-- Note: ./Matroids/foundations.m2 is an upstream in-development module that
-- defines Pasture / Foundation / pasture / pastureMorphism / savePasture /
-- saveFoundation / specificPasture and is not yet integrated into the public
-- Matroids package; it is intentionally not loaded here.  See
--   https://github.com/jchen419/Matroids-M2
-- for upstream development.

tutteUnisum = method(Options => {BaseRing => tutteRing});
tutteUnisum (ZZ, ZZ, ZZ, ZZ) := RingElement => opts -> (r, k, h, n) -> (
    tutteUniform(r, h) * tutteUniform(k-r, n-h)
    );

tutte = method(Options => {BaseRing => tutteRing});
tutte CyclicFlats :=  opts -> M -> (
    R := opts.BaseRing;
    evalValInvariant(M, tutteUniform, tutteCuspidal, tutteUnisum, BaseRing => R)
    );
    

-- End CyclicFlats Code -------------------------------------------------------

--load "./Matroids/doc-Matroids.m2"

--load "./Matroids/tests-Matroids.m2"


end--
restart
loadPackage(     "CyclicFlats", Reload => true)
uninstallPackage "CyclicFlats"
installPackage   "CyclicFlats"
installPackage(  "CyclicFlats", RerunExamples => true)
viewHelp         "CyclicFlats"
check            "CyclicFlats"

-- TODO: Update documentation
