newPackage("Matroids",
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
	"Matroid",
	"matroid"
}


Matroid = new Type of HashTable
Matroid.synonym = "matroid"

globalAssignment Matroid
net Matroid := M -> (
	net ofClass class M | " of rank " | toString(M.rank) | " on " | toString(#M.groundSet) | " elements"
)

Matroid == Matroid := (M, N) -> M.groundSet === N.groundSet and set bases M === set bases N

matroid = method(Options => {EntryMode => "bases", ParallelEdges => {}, Loops => {}})
matroid (List, List) := Matroid => opts -> (E, L) -> (
	L = unique L;
	if #L > 0 and not instance(L#0, Set) then L = indicesOf(E, L);
	G := set(0..<#E);
	B := if opts.EntryMode == "bases" then ( if #L == 0 then error "matroid: There must be at least one basis" else L )
	else if opts.EntryMode == "nonbases" then ( if #L == 0 then {G} else subsets(G, #(L#0)) - set L )
	else if opts.EntryMode == "circuits" then (
		x := getSymbol "x";
		R := QQ(monoid[x_0..x_(#E-1)]);
		I := monomialIdeal({0_R} | L/(c -> product(c/(i -> R_i))));
		allVars := product gens R;
		(dual I)_* / (g -> set indices(allVars//g))
	);
	M := new Matroid from {
		symbol groundSet => G,
		symbol bases => B,
		symbol rank => #(B#0),
		cache => new CacheTable from {symbol groundSet => E}
	};
	if opts.EntryMode == "circuits" then (
		M.cache.ideal = I;
		M.cache.circuits = L;
	) else if opts.EntryMode == "nonbases" then M.cache.nonbases = L;
	M
)
matroid List := Matroid => opts -> L -> matroid(sort unique flatten L, L, opts)
matroid (ZZ, List) := Matroid => opts -> (n, L) -> matroid(toList(0..<n), L, opts)
matroid (List, List, ZZ) := Matroid => opts -> (E, N, r) -> ( -- non-spanning circuits
	if #N > 0 and not instance(N#0, Set) then N = N/set;
	spanningCircuits := subsets(E, r+1)/set - set flatten apply(N, c -> apply(subsets(E - c, r+1 - #c)/set, s -> s + c));
	matroid(E, N | spanningCircuits, EntryMode => "circuits")
)
matroid Matrix := Matroid => opts -> A -> (
	k := rank A;
	setRepresentation(matroid(apply(numcols A, i -> A_{i}), (select(subsets(numcols A, k), S -> rank A_S == k))/set), A)
)
matroid Graph := Matroid => opts -> G -> (
	P := opts.ParallelEdges;
	L := opts.Loops/(v -> set{v});
	e := #edges G;
	E := hashTable apply(e, i -> (edges G)#i => i);
	C := getCycles G/(c -> set apply(#c-1, i -> E#(set{c#i, c#(i+1)})));
	for i from 0 to #P - 1 do (
		C = C | select(C, c -> member(E#(P#i), c))/(c -> c - set{E#(P#i)} + set{e+i}) | {set{E#(P#i), e + i}};
	);
	M := matroid(edges G | P | L, C | apply(#L, i -> set{e + #P + i}), EntryMode => "circuits");
	if #L == 0 and #P == 0 then M.cache.graph = G;
	I := id_(ZZ^(#G.vertexSet));
	A := incidenceMatrix G;
	if #P > 0 then A = A | matrix{apply(P/toList, p -> I_{p#0} + I_{p#1})};
	if #L > 0 then A = A | map(ZZ^(numrows A), ZZ^(#L), 0);
	setRepresentation(M, sub(A, ZZ/2))
)
matroid (List, MonomialIdeal) := Matroid => opts -> (E, I) -> (
	allVars := product gens ring I;
	M := matroid(E, (dual I)_* / (g -> set indices(allVars//g)));
	M.cache.ideal = I;
	M
)
matroid Ideal := Matroid => opts -> I -> (
	J := if instance(I, MonomialIdeal) then I else monomialIdeal I;
	-- The following is ~2x faster than isSquareFree
	if (J == I and isSubset(set flatten flatten(J_*/exponents), set{0,1})) then matroid(gens ring J, J)
	else error "matroid: Expected a squarefree monomial ideal"
)

ideal Matroid := MonomialIdeal => M -> ( -- Stanley-Reisner ideal of independence complex
	if M.cache.?ideal then M.cache.ideal else M.cache.ideal = (
		x := getSymbol "x";
		R := QQ(monoid [x_0..x_(#M.groundSet - 1)]);
		dual monomialIdeal({0_R} | apply(bases M, b -> product(toList(M.groundSet - b) /(i -> R_i))))
	)
)

isWellDefined Matroid := Boolean => M -> (
	K := keys M;
	expectedKeys := set {
		symbol groundSet, 
		symbol bases, 
		symbol rank, 
		symbol cache
	};
	if set K =!= expectedKeys then (
		if debugLevel > 0 then (
			added := toList(K - expectedKeys);
			missing := toList(expectedKeys - K);
			if #added > 0 then printerr("isWellDefined: unexpected key(s): " | toString added);
			if #missing > 0 then printerr("isWellDefined: missing keys(s): " | toString missing);
		);
		return false
	);
	if not M.groundSet === set(0..<#M.groundSet) then (
		if debugLevel > 0 then printerr("isWellDefined: expected groundSet to be " | toString set(0..<#M.groundSet));
		return false
	);
	if not (instance(M.bases, List) and all(bases M, b -> instance(b, Set) and isSubset(b, M.groundSet))) then (
		if debugLevel > 0 then printerr("isWellDefined: expected bases to be a list of subsets of groundSet");
		return false
	);
	if not all(M.bases, b -> #b === M.rank) then (
		if debugLevel > 0 then printerr("isWellDefined: expected rank to be the size of all bases");
		return false
	);
	if M.cache.?storedRepresentation then (
		A := M.cache.storedRepresentation;
		if numcols A =!= #M.groundSet or rank A =!= rank M then (
			if debugLevel > 0 then printerr("isWellDefined: storedRepresentation is invalid");
			return false
		);
	);
	 -- circuit elimination
	I := ideal dual M;
	if numgens ideal M < numgens I then I = ideal M;
	R := ring I;
	J := ideal flatten apply(subsets(I_*, 2), p -> (indices gcd(p#0,p#1))/(i -> p#0*p#1//(R_i^2)));
	numgens J == 0 or isSubset(J, I)
)

Matroid _ ZZ := (M, i) -> M.cache.groundSet#i
Matroid _ List := (M, S) -> (M.cache.groundSet)_S
Matroid _ Set := (M, S) -> S/(i -> M.cache.groundSet#i)
Matroid _* := M -> M.cache.groundSet

groundSet = method()
groundSet Matroid := Set => M -> M.groundSet

-- Miscellaneous general purpose helper functions

sizes = L -> L/(l -> #l)

sliceBySize = (s, L) -> partition(l -> #(l*s), L) -- intersects a set against a list of sets, and records sizes

sliceBySizeList = (s, L) -> ( -- intersects a list against a list of lists, and records sizes
	s = set s;
	partition(l -> #(s * set l), L)
) -- note: this is different from sliceBySize(set s, L/set)

-- Begin CyclicFlats Code -----------------------------------------------------


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

    cyclicFlatsAxioms cFlats -> (
        G := keys cFlats;
        P := poset(G, isSubset);
        --Z0
        if not isLattice P then (
            if debugLevel > 0 then printerr("Error: " | toString(P) | " is not a poset under inclusion.")
            return false
            )
        --Z1
        -- TODO: Implement Z1.
        --Z2
        for g in G do (
            for h in principalFilter(P,g) do (
                if (g != h) then(  --maybe figure out a way around this, like just removing g from the principal filter
                    if H#h - H#g == 0 or H#h - H#g >= #(h - g) then (
                        if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom.") -- TODO: Make error message more specific.
                        return false
                        );
                    )
                )
            );
        --Z3
        for g in G do (
            for h in G do (
                rankSum = H#g + H#h;
                pJoin = first posetJoin(P, g, h);
                pMeet = first posetMeet(P, g, h);
                rankJoin = H#(pJoin);
                rankMeet = H#(pMeet);
                if ( rankSum < rankJoin + rankMeet + #(intersect(g,h)) - #(pMeet)) then (
                    if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " does not satisfy axiom.") -- TODO: Make error message more specific.
                    return false
                    );
                );
            );
        true
        )
    if not cyclicFlatsAxioms H then error "Given hashtable " | toString H | " does not satisfy the axioms of a collection of cyclic flats."
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

tuttePolynomialRing := ZZ(monoid(["x","y"]/getSymbol));
tuttePolynomialUniform = method(Options => {BaseRing => tuttePolynomialRing});
tuttePolynomialUniform (ZZ, ZZ) := RingElement => opts -> (k, n) -> (
    R := opts.BaseRing;
    total := sum apply(k, i -> binomial(n-i-2, n-k-1)*R_0^(i+1));
    total += sum apply(n-k, i -> binomial(n-i-2, k-1)*R_1^(i+1));
    total
    );



-- End CyclicFlats Code -------------------------------------------------------

load "./Matroids/doc-Matroids.m2"

load "./Matroids/tests-Matroids.m2"

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
