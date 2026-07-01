newPackage("CyclicFlats",
	AuxiliaryFiles => true,
	Version => "1.0.0",
	Date => "June 2026",
	Authors => {{
		Name => "",
		Email => ""}},
	Headline => "computations with cyclic flats",
	Keywords => {"Matroids"},
	HomePage => ""
)
export {
	"CyclicFlats",
	"cyclicFlats",
        "BaseRing",
        "groundSet",
        "rankSum",
        "cyclicFlatsType",
        "cyclicFlatsAxioms",
        "evalValInvariant"
}

needsPackage "Posets"


CyclicFlats = new Type of HashTable
CyclicFlats.synonym = "cyclicFlats"

globalAssignment CyclicFlats
net CyclicFlats := M -> (
    net ofClass class M | " of rank " | toString(M.rank) | " on " | toString(#M.groundSet) | " elements"
    )

cyclicFlats = method()
cyclicFlats(HashTable) := H -> (
    -- TODO: Axiom checking
    cyclicFlatsType = cFlats -> (
        scanPairs(cFlats, (Flat, Rank) -> (
                if not instance(Flat, Set) then (
                    if debugLevel > 0 then printerr("Error: " | toString(Flat) | " is not a set.");
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

    cyclicFlatsAxioms = cFlats -> (
        G := keys cFlats;
        P := poset(G, isSubset);
        --Z0
        if not isLattice P then (
            if debugLevel > 0 then printerr("Error: " | toString(P) | " is not a poset under inclusion.");
            return false;
            );
        --Z1
        -- TODO: Implement Z1.
        --Z2
        for g in G do (
            for h in principalFilter(P,g) do (
                if (g != h) then(  --maybe figure out a way around this, like just removing g from the principal filter
                    if H#h - H#g == 0 or H#h - H#g >= #(h - g) then (
                        if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom."); -- TODO: Make error message more specific.
                        return false
                        );
                    )
                )
            );
        --Z3
        for g in G do (
            for h in G do (
                rankSum = H#g + H#h;
                pJoin := first posetJoin(P, g, h);
                pMeet := first posetMeet(P, g, h);
                rankJoin := H#(pJoin);
                rankMeet := H#(pMeet);
                if ( rankSum < rankJoin + rankMeet + #(intersect(g,h)) - #(pMeet)) then (
                    if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom."); -- TODO: Make error message more specific.
                    return false;
                    );
                );
            );
        true;
        );
    if not cyclicFlatsAxioms H then error "Given hashtable " | toString H | " does not satisfy the axioms of a collection of cyclic flats.";
    M := new CyclicFlats from {
        symbol groundSet => union keys H,
        symbol rank => max values H,
        symbol cyclicFlats => H
        };
    M
    );

countStressedSubsets = method();
countStressedSubsets(CyclicFlats, ZZ, ZZ) := (M, r, h) -> (
    num := 0;
    scanPairs(M.cyclicFlats, (S, ri) -> if ri == r and #S == h then num += 1);
    num
    );

evalValInvariant (CyclicFlats, Function, Function, Function) := M, Uniform, Cuspidal, Unisum -> (
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
    total += sum apply(1..k, r -> (
                sum apply(r..n, h -> (
                        lam := countStressedSubsets(M, r, h);
                        lam * (Cuspidal(r, k, h, n) - Unisum(r, k, h, n))
                        );
                    );
                );
            );
        total
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
    R = opts.BaseRing;

    alpha = (i, j, r, k) -> (
        if i + j <= k then (R_0 - 1)^(k-i-j)(1-((R_0-1)(R_1-1))^(i-r)) else (R_1 - 1)^(k-i-j)(1-((R_0-1)(R_1-1))^(k-r-j))
        );
    
    total := tutteUniform(k-r, n-h, BaseRing => R) * tutteUniform(r, h, BaseRing => R);
    total += sum apply(r+1..h, i -> (
            sum apply(0..k-r-1, j -> (
                    binomial(h, i) * binomial(n-h, j) * alpha(i, j, r, k)
                    );
                );
            );
        );
    total
    );

tutteUnisum = method(Options => {BaseRing => tutteRing});
tutteUnisum (ZZ, ZZ, ZZ, ZZ) := RingElement => opts -> (r, k, h, n) -> (
    tutteUniform(r, h) * tutteUniform(k-r, n-h)
    );

tutte = method(Options => {BaseRing => tutteRing});
tutte CyclicFlats := RingElement => opts -> M -> (
    R = opts.BaseRing
    evalValInvariant(M, tutteUniform, tutteCuspidal, tutteUnisum, BaseRing => R)
    );
    

-- End CyclicFlats Code -------------------------------------------------------

--load "./Matroids/doc-Matroids.m2"

--load "./Matroids/tests-Matroids.m2"

-- Note: ./Matroids/foundations.m2 is an upstream in-development module that
-- defines Pasture / Foundation / pasture / pastureMorphism / savePasture /
-- saveFoundation / specificPasture and is not yet integrated into the public
-- Matroids package; it is intentionally not loaded here.  See
--   https://github.com/jchen419/Matroids-M2
-- for upstream development.

end--
restart
loadPackage(     "CyclicFlats", Reload => true)
uninstallPackage "CyclicFlats"
installPackage   "CyclicFlats"
installPackage(  "CyclicFlats", RerunExamples => true)
viewHelp         "CyclicFlats"
check            "CyclicFlats"

-- TODO: Update documentation
