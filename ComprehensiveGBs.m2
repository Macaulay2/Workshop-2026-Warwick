newPackage(
    "ComprehensiveGBs",
    Version => "0.1",
    Date => "",
    Headline => "A package for computing Comprehensive Groebner Bases (CGBs)",
    Authors => {
        { Name => "Lorenzo De Biase", Email => "lorenzo.debiase@enea.it", HomePage => "https://sites.google.com/view/lorenzodebiase/"},
        { Name => "Weijia Wang", Email => "weijia.wang@lip6.fr", HomePage => "https://weijia.perso.lip6.fr/"},
        { Name => "Angelo El Saliby", Email => "angelo.el.saliby@mis.mpg.de", HomePage => "angeloelsaliby.github.io"},
        { Name => "Oliver Clarke", Email => "oliver.clarke@durham.ac.uk", HomePage => "https://www.oliverclarkemath.com"},
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""},
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => "https://sites.google.com/view/mariaagustinacagliero/"},
        { Name => "Giulia Gaggero", Email => "gaggerog@mcmaster.ca", HomePage => ""},
        { Name => "Woody Cohen", Email => "2597103@swansea.ac.uk", HomePage => ""}
    },
    Keywords => {""},
    AuxiliaryFiles => false,
    PackageImports => {"MinimalPrimes", "RealRoots"},
    DebuggingMode => true
)

export {
    "CGBMain",
    "CGB",
    "cgbOnGraph",
    "ReduceStrata",
    "CGBFromTriple",
    "PGBMain",
    "MDBasis",
    "Depth",
    "CheckAssumption"
} -- functions, objects to export

protect CGBMainTriples
protect Loops

-* Code section *-

CGBTriple = new Type of HashTable

protect coefficientsRing  --Probably needs to be changed
                          --b/c too similar to coefficientRing
protect totalRing
protect flattenedRing
protect triple            --Probably needs to be changed b/c
                          --too generic?

ringOrder = method(); -- returns the monomial order of a polynomial ring
ringOrder PolynomialRing := List => R -> (
    order := select(toList (options R).MonomialOrder, orderEntry -> not member(first orderEntry, {MonomialSize, Position}));
    n := numgens R;
    apply(order, orderEntry -> (
        if first orderEntry === Weights then (
            -- For U = QQ[a]; R = U[x,y,z, MonomialOrder => {Lex => 1, GLex}];
            -- {Lex => 1, GLex} unexpectedly expands to {Lex => 1, Weights => {1,1,1}, Lex => 2}.
            -- The bug is confirmed and will be fixed in future versions of Macaulay2: https://github.com/Macaulay2/M2/pull/4673
            -- Anyway, we ignore the unused weights as a hotfix for now.
            Weights => take(last orderEntry, min(n, #last orderEntry))
        ) else (
            n = n - if instance(last orderEntry, ZZ) then last orderEntry else #last orderEntry;
            orderEntry
        )
    ))
);

CGBFromTriple = method(); --Constructor for a CGBTriple starting from
                          --a list {E, F, G} where V(E)\V(F) is the
                          --parametric strata and G is the set of
                          --polynomial to be studied on it.

CGBFromTriple List := CGBTriple => (L) -> (
    if length L != 3 then error("expected a triple {E, N, F} of three lists");
    if length L_0 == 0 then error("E must not be empty; use {0} when no equality constraints are present");
    if length L_2 == 0 then error("F must not be empty");
    if any(L_1, n -> zero n) then error("Please remove zeros from N");
    R := ring L_2_0;
    return new CGBTriple from {
        "triple" => L,
        "cgbData" => CGBDataFromRings(R)};
);

CGBDataFromRings = method();

CGBDataFromRings Ring := CGBData => (R) -> (
    KU := coefficientRing R;
    K := coefficientRing KU;
    n := numgens R;
    m := numgens KU;
    x := local x;
    u := local u;
    l := local l;
    RExt := K[l, x_1..x_n, u_1..u_m, MonomialOrder => {Lex => 1} | ringOrder R | ringOrder KU];
    RFlat := K[x_1..x_n, u_1..u_m, MonomialOrder => ringOrder R | ringOrder KU];
    RExt' := KU[l, x_1..x_n, MonomialOrder => {Lex => 1} | ringOrder R];
    RFlatl := RFlat[l];
    RtoRExt := map(RExt, R, drop(gens RExt, 1));
    RExttoRFlatl := map(RFlatl, RExt, gens RFlatl | gens coefficientRing RFlatl);
    RExttoRExt' := map(RExt', RExt, gens RExt'| gens coefficientRing RExt');
    RExttoR := map(R, RExt, {1} | gens R | gens coefficientRing R);
    KUtoRFlat := map(RFlat, KU, take(gens RFlat, -#gens KU));
    RFlattoR := map(R, RFlat, gens R | gens coefficientRing R);
    KUtoR := map(R, KU, gens coefficientRing R);
    RtoRFlat := map(RFlat, R, gens RFlat);

    new CGBData from {
        "R"             => R,
        "RExt"          => RExt,
        "RFlat"         => RFlat,
        "RExt'"         => RExt',
        "KU"            => KU,
        "RFlatl"        => RFlatl,
        "RtoRExt"       => RtoRExt,
        "RExttoRFlatl"  => RExttoRFlatl,
        "RExttoRExt'"   => RExttoRExt',
        "RExttoR"       => RExttoR,
        "KUtoRFlat"     => KUtoRFlat,
        "RFlattoR"      => RFlattoR,
        "KUtoR"         => KUtoR,
        "RtoRFlat"      => RtoRFlat
    }
);


listOfFactors = method() -- returns the list of factors of a ring element
listOfFactors (RingElement) := (h) -> (
    hfac := factor h;
    select(apply(#hfac, i -> hfac#i#0), t -> not isConstant t)
);

squareFreePart = method() -- returns the square free part of a ring element
squareFreePart (RingElement) := (h) -> (
    if zero h then return h;
    R := ring h;
    f := product listOfFactors h;
    return f_R
);



isConsistent = method(); -- returns whether or not rad(E) intersect N is empty
isConsistent (List, List) := (E, N) -> (
    I := radical ideal E;
    any(N, p -> not isMember(p, I))
);

isConsistentRabinowitsch = method(); -- isConsistent, using the Rabinowitsch trick
isConsistentRabinowitsch (List, List) := (E, N) -> (
    if isEmpty (E|N) then(return false);
    if isEmpty E then(
        if zero first N then error("Please remove zeros from N");
        return true;
    );
    if isEmpty N then(return false);
    R := ring E_0;
    u := local u;
    y := local y;
    S := (baseRing R)[u_1..u_(numgens R), y];
    M := map(S, R, take(gens S, numgens R));
    any(N, f -> not isMember(1, ideal((M \ E)|{(M(f)*last(gens S)-1)})))
)
--R=QQ[x,y]
--E={x+y}
--N={y^2}
--isConsistentRabinowitsch(E,N)


diffLocallyClosed = method(
    Options => {
        Strategy => "Rabinowitsch" -- "radical" or "Rabinowitsch"
    }
);
diffLocallyClosed (Sequence, Sequence) := opts -> (A, B) -> (
    result := {(A#0 | {B#1}, A#1)} | apply(B#0, p -> (A#0, A#1 * p));
    if opts.Strategy == "radical" then (
        select(result, t -> isConsistent(t#0, {t#1}))
    )
    else if opts.Strategy == "Rabinowitsch" then (
        select(result, t -> isConsistentRabinowitsch(t#0, {t#1}))
    )
    else (
        error "Unknown strategy for diffLocallyClosed"
    )
);

diffConstructiblebyLocallyClosed = method(
    Options => {
        Strategy => "radical"
    }
);
diffConstructiblebyLocallyClosed (List, Sequence) := opts -> (C, LC) -> (
    flatten apply(C, t -> diffLocallyClosed(t, LC, opts))
);


-- store all the maps and rings of a CGB computation in a object
CGBData = new Type of HashTable

CGBMain = method(
    Options => {
        ReduceStrata => false,
        Strategy => "Rabinowitsch",
        Verbose => false,
        Depth => -1,
        CheckAssumption => true
    }
); -- Initialises CGBMainRec

CGBMain (List) := o -> (F) -> (
    R := ring first F;
    KU := coefficientRing R;
    S := first entries eliminateVariables F;
    cgs := CGBMain(F, S, o ++ {CheckAssumption => false});
    if #S == 0 then return cgs;
    {({0_KU}, S, {1_R})} | cgs
)
CGBMain (List, List) := o -> (F, S) -> (
    R := ring first F;
    KU := coefficientRing R;
    S' := apply(S, s -> (
        s' := sub(s, R);
        if not liftable(s', KU) then
            error("S must consist of polynomials in the parameters; found " | toString s);
        lift(s', KU)
    ));
    if o.CheckAssumption then (
        -- V(S) is contained in V(<F> cap k[U]) <=> (S, <F> cap k[U]) is inconsistent
        if isConsistentRabinowitsch(S', first entries eliminateVariables F) then
            error("V(S) is not contained in V(ideal F cap k[U]); pass CheckAssumption => false to skip this check");
    );
    cgbData := CGBDataFromRings R;
    cgs := CGBMainRec(F, S', {}, cgbData,
        ReduceStrata => o.ReduceStrata,
        Strategy => o.Strategy,
        Verbose => o.Verbose,
        Depth => o.Depth
    );
    apply(cgs, t -> (if #(t#0) == 0 then {0_KU} else t#0, t#1, t#2))
)

CGBMainRec = method(
    Options => {
        ReduceStrata => false,
        Strategy => "Rabinowitsch",
        Verbose => false,
        Depth => -1
    }
);
CGBMainRec (List, List, List, CGBData) := o -> (F, S, memo, cgbData) -> (
    R := cgbData#"R";
    RExt := cgbData#"RExt";
    RFlat := cgbData#"RFlat";
    RExt' := cgbData#"RExt'";
    KU := cgbData#"KU";
    RFlatl := cgbData#"RFlatl";
    RtoRExt := cgbData#"RtoRExt";
    RExttoRFlatl := cgbData#"RExttoRFlatl";
    RExttoRExt' := cgbData#"RExttoRExt'";
    RExttoR := cgbData#"RExttoR";
    KUtoRFlat := cgbData#"KUtoRFlat";
    RFlattoR := cgbData#"RFlattoR";
    KUtoR := cgbData#"KUtoR";
    RtoRFlat := cgbData#"RtoRFlat";

    S = first entries gens gb ideal S;
    if o.Verbose then (
        print("Computing CGB for F = " | toString F | " and S = " | toString S);
    );
    if 1 % (ideal S) == 0 then (
        return {}
    );
    l := first gens RExt;
    A := apply(F, i -> l * RtoRExt(i));
    B := apply(S, i -> (l-1) * RtoRExt(i));
    G := (entries gens gb(ideal join(A, B)))_0; -- isn't G in RExt? why do we substitute it in the line below? Let's clean it up without a sub

    n := numgens R;
    pruneG := select(G, g -> (
        (first first exponents(leadMonomial sub(g, RExt))) > 0) and
        any(exponents(sub(leadCoefficient RExttoRFlatl(g), RFlat)), i -> any(i_(toList(0..(n-1))), i -> i > 0)));
    pruneG = apply(pruneG, g -> leadCoefficient RExttoRExt'(g));
    h := lcm(pruneG | {1_KU});
    for i in 0..(#(factor h)-1) do (
        if isConstant (factor h)#i#0 then(
            h = h//(factor h)#i#0;
        )
    );

    if o.ReduceStrata then (
        memo = memo | {
            (S, {h},
                for g in G list (
                    g' := RExttoR(g);
                    if zero g' then continue;
                    g')
            )
        };
    );

    if pruneG == {} then (
        if o.ReduceStrata then (
            return memo
        ) else (
            return {
                (S, {h},
                    for g in G list (
                        g' := RExttoR(g);
                        if zero g' then continue;
                        g')
                )
            }
        )
    );

    -- H := pruneG; -- (takes too long to terminate if we do not factor h)
    -- H := unique apply(pruneG, g -> squareFreePart g); -- (takes a bit longer to terminate)

    H := listOfFactors h;
    if o.ReduceStrata then (
        diffset := {};
        for hi in H do (
            diffset = {({hi}, 1_(KU))};
            for t in memo do (
                diffset = diffConstructiblebyLocallyClosed(diffset, (t#0, first t#1), Strategy => o.Strategy);
                if isEmpty diffset then (
                    break
                );
            );
            if isEmpty diffset then (
                continue;
            );
            if o.Depth != 0 then (
                memo = CGBMainRec(F, append(S, hi), memo, cgbData, o ++ {Depth => o.Depth -1});
            )
        );
        return memo
    ) else (
        return {
            (S, {h},
                for g in G list (
                    g' := RExttoR(g);
                    if zero g' then continue;
                    g')
            )
        } | if o.Depth == 0 then {} else flatten apply(H, hi -> CGBMainRec(F, append(S, hi), memo, cgbData, o ++ {Depth => o.Depth -1}))
    );
);


-*

Notes on Optimisation:

-- profiling - see what else is taking time

needsPackage "ComprehensiveGBs"
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
profile CGBMain(F, {});
profileSummary

*-

CGB = method( Options => {
    ReduceStrata => false,
    Strategy => "Rabinowitsch",
    Verbose => false,
    Depth => -1
})
CGB(List) := o -> F -> (
    s := first entries eliminateVariables(F);
    result := s;
    G := CGBMain(F, s,
        ReduceStrata => o.ReduceStrata,
        Strategy => o.Strategy,
        Verbose => o.Verbose,
        Depth => o.Depth,
        CheckAssumption => false
    );
    for i in G do (
        result = result|(i_2);
    );

    unique result
)


eliminateVariables = method()
eliminateVariables(List) := F -> (
    R := ring first F;
    n := numgens(R);
    C := coefficientRing R;
    m := numgens C;
    x := local x;
    u := local u;
    K := coefficientRing C;
    S := K[x_1..x_n, u_1..u_m, MonomialOrder => ringOrder R | ringOrder C];
    U := gens C;
    X := gens R;
    l1 := for i from 0 to m-1 list U_i => S_(i+n);
    l2 := for j from 0 to n-1 list X_j => S_j;
    F' := apply(F, h -> sub(h, l1|l2));
    F'gbgens := gens gb(ideal(F'));
    variableBlocks := select(ringOrder R, orderEntry -> first orderEntry =!= Weights);
    S' := selectInSubring(#variableBlocks, F'gbgens);
    mm := map(C, ring S',
        toList(n:0)|gens C
    );
    mm(S')
)


cgbOnGraph = method()
cgbOnGraph(List, ZZ) := (G, d) -> (
    V := sort G_0;
    E := G_1;
    x := local x;
    w := local w;
    S := QQ[toSequence apply(E, l -> w_l)];
    R := S[x_(V_0, 1)..x_(V_(#V-1), d)];
    F := for i in E list(sum(1..d, k -> (R_(d*(i_0-V_0)+k-1)-R_(d*(i_1-V_0)+k-1))^2)-S_(position(E, j -> j === i)));
    (F, CGBMain F)
)

-- Given two lists A and B return the list
-- {a*b s.t. a in A and b in B}
totalListProduct = method();
totalListProduct (List, List) := (A, B) -> (
    if length A == 0 then (
        return B
    );
    if length B == 0 then (
        return A
    );
    return flatten(
        for a in A list(
            for b in B list (
                a*b
            )
        )
    )
);


--------------------------------------------------
-- Implementing definition 4.1 of 
-- "An efficient algorithm for computing a 
-- comprehensive Gröbner system of a parametric 
-- polynomial system", D. Kapur Y. Sun D. Wang, 
-- J. of Symbolic Computation issue 49, 2013
--------------------------------------------------
MDBasis = method();
MDBasis (List) := (G) -> (
    F := G;
    if length F == 0 then (
        return {}
    );
    -- Section 7.1, first heuristic
    simpler := lc -> max({0} | apply(listOfFactors lc, f -> first degree f));
    -- Section 7.1, second heuristic
    lpps := apply(G, leadMonomial);
    minimal := select(G, g -> not any(lpps, m -> m != leadMonomial g and (leadMonomial g) % m == 0));
    freq := tally apply(minimal, g -> toString leadCoefficient g);
    sharedCount := lc -> if freq#?(toString lc) then freq#(toString lc) else 0;
    -- order the input by those two heuristics;
    -- if there are still ties, order by the keys (chosen purely arbitrarily) after them
    F = sort(F, g -> (lc := leadCoefficient g; (- sharedCount lc, simpler lc, #terms lc, first degree lc, toString g)));
    Basis := {first F};
    F = delete(first F, F); 
    for g in F do ( --loop through elements of G
        --print("Deleting ", g, "from ", F);
        F = delete(g, F); 
        toAdd := true; --At the end of the loop, if LT_x(g) is not already implied 
                       --by elements in Basis, we should add g to our Basis
        for f in Basis do (
            --print(f, Basis);
            LTg := leadMonomial(g);
            LTf := leadMonomial(f);
            if LTg % LTf == 0 then (
                toAdd = false; --LTg is already in Basis, exit the loop and do not add g to Basis
                break
            )  
            else if LTf % LTg == 0 then ( --LTg divides something in Basis, so it can replace it
                --print("Deliting ", f, " from ", Basis, " and adding ", g );
                Basis = unique(delete(f, Basis) | {g});
                toAdd = false; --avoid adding g multiple times
                continue --might happen that LTg divides other leading terms in Basis
            );
        );
        if toAdd then ( -- LTg is not implied by anything in Basis
            Basis |=  {g};
        );
    );
    return Basis
);


--------------------------------------------------
--Implementing algorithm in section 4.1 of 
--"An efficient algorithm for computing a 
--comprehensive Gröbner system of a parametric 
--polynomial system", D.Kapur Y. Sun D. Wang, 
--J. of Symbolic Computation issue 49, 2013
--------------------------------------------------
PGBMain = method();
PGBMain (CGBTriple) := T -> (
    {E, N, F} := T#"triple";
    cgbData := T#"cgbData";
    R:=cgbData#"R";
    RExt:=cgbData#"RExt"; 
    RFlat:=cgbData#"RFlat";
    RExt':=cgbData#"RExt'";
    KU:=cgbData#"KU";
    RFlatl:=cgbData#"RFlatl";
    RtoRExt:=cgbData#"RtoRExt";
    RExttoRFlatl:=cgbData#"RExttoRFlatl";
    RExttoRExt':=cgbData#"RExttoRExt'";
    RExttoR:=cgbData#"RExttoR";
    KUtoRFlat:=cgbData#"KUtoRFlat";
    RFlattoR:=cgbData#"RFlattoR";
    KUtoR:=cgbData#"KUtoR";
    RtoRFlat:=cgbData#"RtoRFlat";
    --print(E, length N);
    if not(consistencyCheckAllTogether(E, N)) then (
        return {} --The domain is empty
    );
    --Compute the GB of union(E, F), but viewing the parameters as variables
    G := first entries gens gb ideal ((KUtoRFlat \ E) | (RtoRFlat \ F));
    if member(sub(1, RFlat), G) then (
        return {{E, N, {promote(1, R)}}} --Trivial case where the vanishing set is empty
    );
    Gr := for g in G list ( --The polynomials in G that only contain the parameters
        l := lift(RFlattoR(g), KU, Verify =>false);
        --lift() with Verify=>false returns Null when the lift is not possible
        --i.e. when the polynomial contains something other than parametetrs
        if instance(l, Nothing) then (continue);
        l
    );
    -- By convention, an empty list for a GB means that the 
    -- corresponding vanishing set is the whole space, 
    -- which is equivalent to only containing the 0 element.
    -- To keep track of the original rings down the line and in the output, 
    -- we never return an empty GB.
    if length Gr == 0 then (
        Gr = {0_KU}; 
    );
    productList := unique(totalListProduct(Gr, N)); --The list obtained by multiplying every element in Gr with every element in N
    if length(productList) == 0 then (
        productList = {0_KU};
    );
    PGB := {};
    if consistencyCheckAllTogether (E, productList) then (
        PGB = {{E, productList, {1_R}}};
    );
    if not(consistencyCheckAllTogether(Gr, N)) then (
        return PGB
    );
    --Elements of GB that do not only contain parameters
    Gr' := new Set from (KUtoR \ Gr);
    listDiff := select(RFlattoR \ G, g -> not Gr'#?g);
    Gm := MDBasis(listDiff);
    H := unique flatten apply(Gm, g -> listOfFactors(leadCoefficient(sub(g, R))));
    h := squareFreePart lcm(H | {1_KU});
    productList = unique(apply(totalListProduct(N, {sub(h, KU)}), i -> squareFreePart(i)));
    if consistencyCheckAllTogether(Gr, productList) then (
        PGB = unique(PGB | {{Gr, productList, if length Gm == 0 then {0_R} else Gm}});
    );

    for i in 0..(length(H)-1) do (
        -- Both CCheck and ICheck require E to be a Groebner basis of <E>!
        E' := first entries gens gb ideal unique(Gr | {H_i});
        if length E' == 0 then (
            E' = {0_KU};
        );
        if i == 0 then (
            PGB = unique(PGB | PGBMain(CGBFromTriple({
            E',
            N, 
            listDiff}
            )))
        ) else (
        PGB = unique(PGB | PGBMain(CGBFromTriple({
            E',
            unique(totalListProduct(N, {squareFreePart(product(H_{0..(i-1)}))})), 
            listDiff}
        ))));
    );

    return PGB  
);

PGBMain List := F -> (
    if #F == 0 then error("List must be non-empty");
    R := ring first F;
    U := coefficientRing R;
    PGBMain(CGBFromTriple({{0_U}, {1_U}, F}))
    )



-----------------------------
--zeroDimCheck if for those
--cases in which <E> is
--zero dimensional.
--It uses RealRoots.
-----------------------------

zeroDimCheck = method();
zeroDimCheck (List, RingElement) := (E, f) -> (
    I := ideal E;
    pf := characteristicPolynomial(f, I);
    d := first degree pf;
    lambda := first gens ring pf;
    if pf == lambda^d then
        false --inconsistent
    else
        true --consistent
);

-----------------------------
--CCheck if for those
--cases in which <E> is
--of positive dimensional.
-----------------------------

CCheck = method();
CCheck (List, RingElement) := (E, f) -> (
    R := ring f;
    U := gens R;
    supports := apply(E, g -> (
        if g == 0 then continue;
        e := first exponents(leadMonomial g);
        select(0..(#e-1), i -> e_i != 0)
    ));

    V := {};

    for i from 0 to (#U - 1) do (
        candidate := V | {i};

        if not any(supports, S -> all(S, j -> member(j, candidate))) then (
            V = candidate;
        );
    );
    alpha := apply(numgens R, i -> random(-100,100));


    -*
    remaining := select(0..(#U-1), i -> not member(i,V));

    newR := coefficientRing R[apply(remaining, i -> U_i)]; --
    newU := gens newR;

    images := toList  apply(0..(#U-1), i -> (
        if member(i,V) then (
            alpha_(position(V, j -> j == i))
        ) else (
            newU_(position(remaining, j -> j == i))
        )
    ));
    *-

    phi := map(R,R,for i from 0 to numgens R-1 list if member(i, V) then alpha_i else R_i);

    spE := gb (ideal apply(E, g -> phi(g)) + ideal(for i in V list R_i));
    -- the above is a little different from KSW where they restrict to a smaller ring
    -- and check that spE is zero dimensional there
    -- Here we add in the variables in order to avoid constructing a new polynomial ring
    -- and hopefully the GB computation is just as fast

    fAlpha := phi(f);
    -- fAlpha = sub(fAlpha, newR); -- shouldn't need this
    GspE := flatten entries gens spE;

    if dim( ideal(GspE)) == 0 and zeroDimCheck(GspE, fAlpha) then (
        return true; -- certifies consistency
    );
    return false -- unknown consistency (i.e., it could still be consistent)
  
);



ICheck = method(
    Options => {
        Loops => infinity
    }
);

ICheck (List, RingElement) := o -> (E, f) -> (
    if zero f then (
        return true; -- certifies inconsistency
    );
    -- we do the computation in the quotient ring R/<E>
    -- this avoids extra costs when doing s := p^2 in the main loop
    Q := (ring f) / ideal E;
    if zero promote(f, Q) then (
        return true; -- certifies inconsistency
    );
    if o.Loops === infinity then (
        return not isConsistentRabinowitsch(E, {squareFreePart f}); -- certifies inconsistency/consistency
    );
    factors := listOfFactors f;
    promoted := apply(factors, g -> promote(g, Q));
    -- before performing ICheck on the input f, we first perform ICheck on the factors of f
    -- this is a not-too-expensive heuristic, but it proves very helpful for S5 and P3P when Loops is set to 4
    candidates := if #factors == 0 then {promote(f, Q)}
        else if #factors == 1 then promoted
        else sort(promoted, z -> #terms z) | {promote(product factors, Q)};
    for p in candidates do (
        if zero p then (
            return true; -- certifies inconsistency
        );
        for i from 1 to o.Loops do (
            s := p^2;
            if zero s then (
                return true; -- certifies inconsistency
            );
            if s == p then break;
            p = s;
        );
    );

    return false; -- unknown consistency
);

----------------------------------------
--THE FOLLOWING PUTS TOGETHER ZERODIMCHECK
--CCHECK AND ICHECK
--1)check whether f is already in <E>
--2)determine the dimension of <E>
--3) zeroDimCheck or CCheck
--4) if CCheck is not enough, do ICheck
----------------------------------------

consistencyCheckAllTogether = method(
    Options => {
        Loops => infinity
    }
);

consistencyCheckAllTogether (List, RingElement) := o -> (E, f) -> (
    if (f % ideal E) == 0 then (
        print "inconsistent: direct ideal membership check was used";
        return false; -- inconsistent
    );

    d := dim ideal E;

    if d == 0 then (
        print "zeroDimCheck was used";
        return zeroDimCheck(E,f);
    );

    if CCheck(E,f) then (
        print "consistent: CCheck was used";
        return true; -- consistent
    );

    if ICheck(E,f, Loops => o.Loops) then (
        print "inconsistent: ICheck was used";
        return false; -- inconsistent
    );

    if o.Loops === infinity then (
        -- ICheck also checks consistency when Loops is infinity
        -- so if we reach this point, f is not in rad(E)
        return true; -- consistent
    );

    print "General check was used";
    return null; -- temporary
);

-- Cannot have ideal E = (0) or ideal F = (0)
consistencyCheckAllTogether (List, List) := o -> (E, N) -> (
    if length E == 0 then (
      if length N == 0 then (
        return false
      );
    ) else (
      KU := ring E_0;
      if ideal E == ideal(0_KU) or ideal N == ideal(0_KU) then (
        if ideal N == ideal(0_KU) then return false;
        return true);
    );
    undecided := false;
    for f in N do (
        check := consistencyCheckAllTogether(E, f, Loops => o.Loops);

        if check === true then (
            return true;
        );

        if instance(check, Nothing) then (
            undecided = true;
        );
    );

    if undecided then (
        return isConsistentRabinowitsch(E, N)
    );

    return false
);




-* Documentation section *-

beginDocumentation()

doc ///
  Key
    ComprehensiveGBs
  Headline
    a package for computing Comprehensive Groebner Bases (CGBs).
  Description
    Text
      This package provides the implementations of two differnt algorithms for computing a comprehensive Gröbner system and a
      comprehensive Gröbner basis of a parametric ideal. In the following we refer to Section 2 of @HREF("#ref1","[1]")@.
      
      Let $k$ be a field, $R$ be the polynomial ring $k[U]$ in the parameters $U=\{u_1,\ldots,u_m\}$, and $R[X]$ be the polynomial ring
      over $R$ in the variables $X=\{x_1,\ldots,x_n\}$ and $X\cap U=\emptyset$.
      Call $L$ the algebraic closure of $k$. Given $a \in L^m$, the specialization homomorphism of $R$ induced by $a$ is
      $\sigma_a:R\rightarrow L$, $\sigma_a(f)=f(a)$. $\sigma_a$ extends canonically to a homomorphism $\sigma_a:R[X]\rightarrow L[X]$
      by applying $\sigma_a$ coefficient-wise.
      For an $E\subseteq R=k[U]$, the variety defined by $E$ in $L^m$, denoted by $V(E)$ is
      $V(E)=\{a\in L^m :\sigma_a(f)=0 \text{ for all } f \in E \}.$

      A set $A\subseteq L^m$ is said constructible if it exists a pair of finite sets of polynomials $(E,N)$ such that
      $A=V(E)\setminus V(N)$, where $E,N\subseteq k[U]$.

      Let $F$ be a subset of $R[X]$, $E_1,N_1,\ldots, E_t,N_t$ be subsets of $R=k[U]$, $G_1,\ldots,G_t$ be subsets of $R[X]$,
      and S a subset of $L^m$ such that $S\subseteq (V(E_1)\setminus V(N_1) \cup \ldots \cup V(E_t)\setminus V(N_t)$. A finite set
      $\mathcal{G} = \{(E_1,N_1,G_1),\ldots,(E_t,N_t,G_t)\}$ is called a comprehnsive Gröbner system on $S$ for $F$ if
      $\sigma_a(G_i)$ is a Gröbner basis of the ideal $(\sigma_a(F))\subseteq L[X]$ for $a \in V(E_i) \setminus V(N_i)$ and
      $i=1,\ldots,t$. Each $(E_i,N_i,G_i)$ is called a branch of $\mathcal{G}$. In particular, if $S=L^m$, then $\mathcal{G}$ is
      called a comprehensive Gröbner system for F.

      Given $S$ a basis of the elimination ideal of $(F)\cap k[U]$, a comprehenvive Gröbner basis $\mathcal{B}$ for $F\subseteq R[X]$
      is the union of all the sets $G_i$ in a comprehensive Gröbner system $\mathcal{G}$ for F on $S$. Notice that, $(\sigma_a(F))=(1)$
      for any $a \in L^m \setminus V(S)$. Therefore, $\mathcal{G} \cup \{(\emptyset,S,S)\}$ is a comprehensive Gröbner system for $F$.
      
    
      The function @TO "CGBMain"@ is the implementation of Algorithm CGBMain of @HREF("#ref2","[2]")@.

      Instead the function @TO "PGBMain"@ corresponds to the Algorithm PGBMain of @HREF("#ref1","[1]")@.
      
  References
      @LABEL("[1]","id" => "ref1")@ Deepak Kapur, Yao Sun, and Dingkang Wang. 2013. An efficient algorithm for computing a comprehensive Gr\"obner system of a parametric polynomial system. In Journal of Symbolic Computation, 49, 27-44.
      @LABEL("[2]","id" => "ref2")@ Akira Suzuki and Yosuke Sato. 2006. A simple algorithm to compute comprehensive Gröbner bases using Gröbner bases. In Proceedings of the 2006 international symposium on Symbolic and algebraic computation (ISSAC '06). Association for Computing Machinery, New York, NY, USA, 326–331. https://doi.org/10.1145/1145768.1145821
    
///



doc ///
  Key
    "OlliesDocPage"
  Headline
    A small example
  Description
    Text 
      Description of the page you can insert some code snippets too:
      Here is a ring $R = \QQ[a,b][x,y]$ with a Lex monomial order ..
    Example
      R = QQ[a,b][x,y, MonomialOrder => Lex]
      F = {a*x + b*y}
      CGBMain(F, {})
    Text
      Amazing!
      A link to the package: @TO "ComprehensiveGBs"@.
      Sometimes we talk about @TT "true"@ things.
      
  SeeAlso
    ComprehensiveGBs
///

doc ///
  Key
    CGBMain
    (CGBMain, List, List)
    (CGBMain, List)
    [CGBMain, Strategy]
    [CGBMain, Verbose]
    [CGBMain, ReduceStrata]
    [CGBMain, Depth]
    [CGBMain, CheckAssumption]
  Headline
    a method that computes a Comprehensive Groebner System
  Usage
    CGBMain(F,S)
    CGBMain(F)
  Inputs
    F :List
       a list of polynomials in a ring $R = k[U][X]$
    S :List
       a list of polynomials in a ring $RU = k[U]$
    CheckAssumption=>Boolean
       check that $V(S)\subseteq V(\langle F\rangle\cap k[U])$
    ReduceStrata=>Boolean
       ignore strata that have already been computed
    Strategy=>String
       "radical" or "Rabinowitsch" for checking membership in the radical
    Verbose=>Boolean
       print polynomial lists during computation
    Depth=>ZZ
       maximum recursion depth
  Outputs
    G :List
      of Sequences of the form (E,N,G), where G is a Gröbner basis on the set
      $V(E)\setminus V(N)$
  Description
    Text
      Implementation of the Algorithm proposed by Suzuki and Sato. Given a
      tower polynomial ring $R = k[U][X]$ for $U$ a set of parameters and
      $X$ a set of variables, $F\subset R$ an ideal of variables and
      parameters, and $S\subset k[U]$ an ideal satisfying $V(S)\subseteq
      V(\langle F\rangle\cap k[U])$, CGBMain takes $F$ and $S$ as inputs
      and returns a comprehensive Groebner system on $V(S)$. The function
      itself passes $F$ and $S$ to CGBMainRec after initialising various
      objects. As above, the ring must be initialised as a tower ring:
    Example
      R1 = QQ[a,b][x,y]
    Text
      Here $X = \{x,y\}$ and $U = \{a,b\}$. If we wanted to find a
      comprehensive Groebner system over $\mathb{Q}^2$ for
      $F = \langle ax+by\rangle$, we input the following:
    Example
      F1 = {a*x+b*y}
      S1 = {}
      CGBMain(F1,S1)
    Text
      CGBMain has several options: ReduceStrata, Strategy, Verbose, and
      Depth.

      ReduceStrata is an option to ignore computations on strata which
      have already been considered. This value is set to false by default.
      For smaller examples, changing this to true can reduce computation
      times, as for the following example. It will also give more easily
      parsable results.
    Example
      R2 = QQ[a,b][x,y,z];
      F2 = {x^2-a,y^3-b,x+y-z};
      S2 = {};
    Text
      The option is false by default as the speed-up is not always
      guaranteed. For the example below, which will not be computed to save
      time, the reader may verify the option being false has an execution
      time of less than a minute. Setting ReduceStrata to true increases
      this execution time significantly, in fact, we could not get the
      computation to terminate.
    Example
      R3 = QQ[a,b][x,y,z,s, MonomialOrder => Lex];
      f=(x-a)^2+b*y^2+b;
      F3 = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
    Text
      The option @TO "Strategy"@ depends on @TO "ReduceStrata"@, and has
      two valid values: "radical" and "Rabinowitsch". The former reduces
      strata by directly computing radicals of ideals, and the latter
      utilises the Rabinowitsch trick. The latter is, in general,
      considerably faster.

      Setting @TO "Verbose"@ to @TT "true"@ will display the current
      polynomial lists $F$ and $S$ in the internal computation.
    Example
      CGBMain(F1,S1,Verbose=>true)
    Text
      The option @TO "Depth"@ sets a bound for the recusion depth of the
      algorithm. For instance setting it to zero will return one the
      generic stratum.
    Example
      for i from 0 to 3 do print (i, netList CGBMain(F1, S1, Depth => i))
    Text
      When the function is about to recuse, the
      value of the depth option is checked, if the value is zero then
      the function stop there. Otherwise, the function decrements the
      depth and recuses. The default value for the depth is minus one,
      which means the depth will never reach zero on recusion.


      @TO "CGBMain"@ can take in one or two lists as inputs.
      When $S$ is not specified, the function returns a comprehensive
      Gröbner system on the whole parameter space, by computing a basis
      $\{s_1,\dots,s_r\}$ of the elimination ideal
      $\langle F\rangle\cap k[U]$, passing that basis as $S$ to CGBMain,
      and prepending the extra segment $(\{0\}, \{s_1,\dots,s_r\}, \{1\})$
      to the output. When $S$ is specified, the function returns a
      comprehensive Groebner system on $V(S)$, under the assumption that
      $V(S)\subseteq V(\langle F\rangle\cap k[U])$. That assumption is
      verified before the computation starts, and an error is raised
      when it fails. If the assumption is known to be true, the option
      CheckAssumption can be set to false to skip the verification step.
  SeeAlso
    CGB
    ReduceStrata
    Strategy
    Verbose
  ///

doc ///
  Key
    ReduceStrata
  Headline
    ignore computations on strata which have already been considered
  Description
    Text
      ReduceStrata is an option to ignore computations on strata which have already been considered. This value is set to false by default. For smaller examples, changing this to true can reduce computation times, as for the following example. It will also give more easily parseable results.
    Example
      R2 = QQ[a,b][x,y,z];
      F2 = {x^2-a,y^3-b,x+y-z};
      S2 = {};
    Text
      The value is false by default as this is not true in general - for the example below (which will not be computed to save time, though the reader may verify if they desire) the option being false has an execution time of less than a minute. Setting ReduceStrata to true increases this execution time significantly (a rough estimate for time has not been found, as the computation takes so long).
    Example
      R3 = QQ[a,b][x,y,z,s, MonomialOrder => Lex];
      f=(x-a)^2+b*y^2+b;
      F3 = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
  SeeAlso
    CGBMain
///

doc ///
  Key
    "CGB Strategy"
  Headline
    how to compute the radical in @TO "ReduceStrata"@
  Description
    Text
      Strategy is an option that depends on @TO "ReduceStrata"@. It is for cheking if a pair $(E,N) \subseteq k[U]$ is consistent, i.e., if $V(E)\backslash V(N)$ is not empty. In order to do that the radical of ideal(E) has to be computed, see Section 5 of @HREF("ref1","1")@ for details.
      Strategy has two valid inputs, being "radical" and "Rabinowitsch" - other inputs will return an error. The former reduces strata by directly computing radicals of ideals, and the latter utilises the Rabinowitsch trick. The latter is, in general, considerably faster.
  References
    @LABEL("[1]","id" => "ref1")@ Deepak Kapur, Yao Sun, and Dingkang Wang. 2013. An efficient algorithm for computing a comprehensive Gr\"obner system of a parametric polynomial system. In Journal of Symbolic Computation, 49, 27-44.
  SeeAlso
    CGBMain
    ReduceStrata
///

doc ///
  Key
    Verbose
  Headline
    a record of CGBMain iterations 
  Description
    Text
      Setting Verbose to True will print whatever $F$ and $S$ that CGBMainRec is currently working on:
    Example
      R1 = QQ[a,b][x,y];
      F1 = {a*x+b*y};
      S1 = {};
      CGBMain(F1,S1,Verbose=>true)
  SeeAlso
    CGBMain
///


doc ///
  Key
    cgbOnGraph
    (cgbOnGraph,List,ZZ)
  Headline
    A method for creating parametrised polynomial systems from a graph and calculating a Comprehensive Groebner basis for them.
  Usage
    (F, GG) = cgbOnGraph(G,d)
  Inputs
    G: List
      A list consisting of a list of vertices and a list of edges.
    d: ZZ
      A postive integer
  Outputs
    F: List
      A list of polynomials
    GG: List
      The Comprehensive Groebner Basis of the polynomials
  Description
    Text
      Let $G=(V,E)$ be graph and fix a positive integer $d$.
      Consider the paramaterised polynomial systems $F=\{f_e\}_{e\in E}\subseteq K[\lambda_e\:e\in E][x_{v,k}:v\in V,1\leq k \leq d]$,
      where $K\in \{\mathbb{C},\mathbb{R}\}$ and
      \[   f_{ij}=\sum_{k=1}^{d}(x_{i,k}-x_{j,k})^2  -\lambda_{ij} \].
      cgbOnGraph returns the polynomial systems $F$ and a Combrehensive Groebner Basis of $F$

    Example
      (F,GG)=cgbOnGraph({{1,2,3},{(1,2),(2,3),(3,1)}},1);
      netList F
      GG_0
    
      --cgbOnGraph({{1,2,3,4},{(1,2),(1,3),(1,4),(2,3),(2,4)}},1)

  Caveat
    This function is not set up to take in Type Graph. User will have to convert to list.
  SeeAlso
    ComprehensiveGBs

///


doc ///
  Key
   MDBasis
  Headline
    a method for computing a minimal Disckson Basis
  Usage
    MDBais(F)
  Inputs
    F: List
      a list of polynomials in a ring $R = k[U][X]$
  Outputs
    G: List
      the minimal Dickson basis of F
  Description
    Text
      Following the Definition 4.1 of @HREF("#ref1","[1]")@, given a sequence F of polynomials in $k[U][X]$, MDBasis(F) returns the minimal Dickson basis of F.
      -- do we want to make the defition explicit? 
  References
    @LABEL("[1]","id" => "ref1")@ Deepak Kapur, Yao Sun, and Dingkang Wang. 2013. An efficient algorithm for computing a comprehensive Gr\"obner system of a parametric polynomial system. In Journal of Symbolic Computation, 49, 27-44.
  SeeAlso
    ComprehensiveGBs
    PGBMain
///


doc ///
  Key
    "CGB"
    (CGB, List)
    [CGB, Strategy]
    [CGB, Verbose]
    [CGB, ReduceStrata]
    [CGB, Depth]
  Headline
    a method that computes a Comprehensive Groebner Basis
  Usage
    G = CGB F
  Inputs
    F :List
       a list of polynomials in a ring $R = k[U][X]$
    ReduceStrata=>Boolean
       ignore strata that have already been computed
    Strategy=>String
       "radical" or "Rabinowitsch" for checking membership in the radical
    Verbose=>Boolean
       print polynomial lists during computation
    Depth=>ZZ
       maximum recursion depth
  Outputs
    G :List
      of polynomials forming a comprehensive Gröbner basis of $\langle F\rangle$
  Description
    Text
      Implementation of the Algorithm proposed by Suzuki and Sato. Given a tower polynomial ring $R = k[U][X]$ for $U$ a set of parameters and $X$ a set of variables, and $F\subset R$ an ideal of variables and parameters, CGB takes $F$ as input and returns a comprehensive Groebner basis of $\langle F\rangle$ over the whole parameter space.
      The function computes a comprehensive Groebner system with CGBMain and returns the union of its Groebner bases, together with a basis of the elimination ideal $\langle F\rangle\cap k[U]$.
      As above, the ring must be initialised as a tower ring:
    Example
      R1 = QQ[a,b][x,y]
    Text
      Here $X = \{x,y\}$ and $U = \{a,b\}$. If we wanted to find a comprehensive Groebner basis over $\mathb{Q}^2$ for $F = \langle ax+by\rangle$, we input the following:
    Example
      F1 = {a*x+b*y}
      CGB F1
    Text
      CGB has several options: ReduceStrata, Strategy, and Verbose. ReduceStrata is an option to ignore computations on strata which have already been considered. This value is set to false by default. For smaller examples, changing this to true can reduce computation times, as for the following example. It will also give more easily parseable results.
    Example
      R2 = QQ[a,b][x,y,z];
      F2 = {x^2-a,y^3-b,x+y-z};
    Text
      The value is false by default as this is not true in general - for the example below (which will not be computed to save time, though the reader may verify if they desire) the option being false has an execution time of less than a minute. Setting ReduceStrata to true increases this execution time significantly (a rough estimate for time has not been found, as the computation takes so long).
    Example
      R3 = QQ[a,b][x,y,z,s, MonomialOrder => Lex];
      f=(x-a)^2+b*y^2+b;
      F3 = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
    Text
      Strategy is an option that depends on ReduceStrata, and has two valid inputs, being "radical" and "Rabinowitsch" - other inputs will return an error. The former reduces strata by directly computing radicals of ideals, and the latter utilises the Rabinowitsch trick. The latter is, in general, considerably faster.
      Setting Verbose to True will print whatever $F$ and $S$ that CGBMainRec is currently working on:
    Example
      CGB(F1,Verbose=>true)
  SeeAlso
    CGBMain
    ReduceStrata
    Strategy
    Verbose
  ///



-* Test section *-
TEST ///
-* Testing ringOrder on various polynomial rings *-
debug needsPackage "ComprehensiveGBs";

RGRevLex = QQ[a..d];
RLex = QQ[a..d, MonomialOrder => Lex];
RGLex = QQ[a..d, MonomialOrder => GLex];
RWeights = QQ[a..d, MonomialOrder => {Weights => {1, 3, 2, 4}, Lex}];
REliminate = QQ[a..d, MonomialOrder => Eliminate 2];
RGroupLex = QQ[a..d, MonomialOrder => GroupLex => 2, Global => false];
RGroupRevLex = QQ[a..d, MonomialOrder => GroupRevLex => 2, Global => false];
RProduct = QQ[a..d, MonomialOrder => ProductOrder {2, 2}];
RBlock = QQ[a..d, MonomialOrder => {Lex => 2, GRevLex => 2}];
RRevLex = QQ[a..d, MonomialOrder => RevLex, Global => false];

assert(ringOrder RGRevLex === {GRevLex => {1, 1, 1, 1}});
assert(ringOrder RLex === {Lex => 4});
assert(ringOrder RGLex === {Weights => {1, 1, 1, 1}, Lex => 4});
assert(ringOrder RWeights === {Weights => {1, 3, 2, 4}, Lex => 4});
assert(ringOrder REliminate === {Weights => {1, 1}, GRevLex => {1, 1, 1, 1}});
assert(ringOrder RGroupLex === {GroupLex => 2, GRevLex => {1, 1}});
assert(ringOrder RGroupRevLex === {GroupRevLex => 2, GRevLex => {1, 1}});
assert(ringOrder RProduct === {GRevLex => {1, 1}, GRevLex => {1, 1}});
assert(ringOrder RBlock === {Lex => 2, GRevLex => {1, 1}});
assert(ringOrder RRevLex === {RevLex => 4});
///


TEST /// 
-* Testing  CGBMain on a*x+b*y *-

Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aP = params#0;
bP = params#1;

aR = promote (aP , Rtest);
bR = promote (bP , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {});

expected1 = ({0_Ptest}, {aP}, {aR*xR + bR*yR});
expected2 = ({aP}, {bP}, {aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({bP, aP}, {1_Ptest}, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///


TEST /// 
-* Testing  CGB on a*x+b*y  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest});

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);
///


TEST /// 
-* Testing cgbOnGraph  on  E = {(1,2)}, V = {1,2} *-

E = {(1,2)};
V = {1,2};
G = {V,E};

(F,GG) = cgbOnGraph(G,2);



Rtest = ring first F;


Stest = coefficientRing Rtest;

x11 = Rtest_0;
x12 = Rtest_1;
x21 = Rtest_2;
x22 = Rtest_3;

w12 = promote(Stest_0,Rtest);

expectedF = {x11^2 - 2*x11*x21 + x21^2 + x12^2 - 2*x12*x22 + x22^2 - w12 };
expectedGG = {
    ({0_Stest}, {1_Stest}, expectedF)
};

assert(F == expectedF);
assert(GG == expectedGG);

///


TEST /// 
-* Testing  CGBMain on a*x+b*y  with Verbose option *-
Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aP = params#0;
bP = params#1;

aR = promote (aP , Rtest);
bR = promote (bP , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {}, Verbose => true);

expected1 = ({0_Ptest}, {aP}, {aR*xR + bR*yR});
expected2 = ({aP}, {bP}, {aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({bP, aP}, {1_Ptest}, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);


///


TEST /// 
-* Testing  CGB on a*x+b*y  with Verbose option  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, Verbose=> true);

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);

///


TEST /// 
-*Testing  CGB on a*x+b*y  with Strategy => "radical" option  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, Strategy=> "radical");

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);
///



TEST /// 
-* Testing  CGB on a*x+b*y  with Strategy => "radical" option *-

Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aP = params#0;
bP = params#1;

aR = promote (aP , Rtest);
bR = promote (bP , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {}, Strategy => "radical");

expected1 = ({0_Ptest}, {aP}, {aR*xR + bR*yR});
expected2 = ({aP}, {bP}, {aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({bP, aP}, {1_Ptest}, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///


TEST /// 
-* Testing  CGBMain on a*x+b*y  with ReduceStrata => true option *-
Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aP = params#0;
bP = params#1;

aR = promote (aP , Rtest);
bR = promote (bP , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {},  ReduceStrata => true);

expected1 = ({0_Ptest}, {aP}, {aR*xR + bR*yR});
expected2 = ({aP}, {bP}, {aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({bP, aP}, {1_Ptest}, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///

TEST /// 
-* Testing  CGBMain on a*x+b*y  with ReduceStrata => true option *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, ReduceStrata=> true);

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected2 or result#1 == expected2);

///

-----------------------------
--TEST for MDBasis
-----------------------------
TEST /// -* Testing MDBasis on {a*x^2 - y, a*y^2 - 1, a*x - 1, (a + 1)*x - y, (a + 1)*y - a} *-
U = U = QQ[a, MonomialOrder => Lex];
R = U[x, y, MonomialOrder => Lex];
G = {a*x^2 - y, a*y^2 - 1, a*x - 1, (a + 1)*x - y, (a + 1)*y - a}
MDBasis(G)
///

-----------------------------------------------
--TEST for MDBasis (KSW, Section 6)
-----------------------------------------------
TEST /// -* Testing MDBasis on {a*x*y + b*x, b*x^2*y + c*z, a*b*x + a*x*y + z, a*y + z, c*x + c*z^2} *-
U = QQ[a, b, c, MonomialOrder => Lex];
R = U[x, y, z, MonomialOrder => Lex];
G = {a*x*y + b*x, b*x^2*y + c*z, a*b*x + a*x*y + z, a*y + z, c*x + c*z^2}
assert(MDBasis(G) == {a*y + z, c*x + c*z^2})
///


------------------------------------------------
--TEST for PGBMain
-- From Example 6.1 of 
-- "An efficient algorithm for computing a 
-- comprehensive Gröbner system of a parametric 
-- polynomial system", D. Kapur Y. Sun D. Wang, 
-- J. of Symbolic Computation issue 49, 2013
------------------------------------------------
TEST /// -* Testing PGBMain on {a*x-, b*y-a, c*x^2-y, c*y^2-x} *-
U := QQ[a, b, c, MonomialOrder => GRevLex]
R := U[x,y,z, MonomialOrder => GRevLex]
G := {a*x-b, b*y-a, c*x^2-y, c*y^2-x}
L := PGBMain(CGBFromTriple({{0_U}, {1_U}, G}))
U' = ring first first first L
R' = ring first last first L
ExpResult = set{
  {
    set ((f -> sub(f, U')) \ {0}),
    set ((f -> sub(f, U')) \ {b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}),
    set ((f -> sub(f, R')) \ {1})
    },
  {
    set ((f -> sub(f, U')) \ {b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}),
    set ((f -> sub(f, U')) \ {b}),
    set ((f -> sub(f, R')) \ {b*y-a, b*x-a*c*y})
  },
  {
    set ((f -> sub(f, U')) \ {b, a}),
    set ((f -> sub(f, U')) \ {c}),
    set ((f -> sub(f, R')) \ {c*x^2-y, c*y^2-x})
    },
  {
    set ((f -> sub(f, U')) \ {c, b, a}),
    set ((f -> sub(f, U')) \ {1_U'}),
    set ((f -> sub(f, R')) \ {y, x})
    }
}

assert( (new Set from for r in L list for p in r list set p) == ExpResult )

///


end--



-* Development section *-
restart
debug needsPackage "ComprehensiveGBs"
check "ComprehensiveGBs"

uninstallPackage "ComprehensiveGBs"
restart
needsPackage "ComprehensiveGBs"
installPackage "ComprehensiveGBs"
viewHelp "ComprehensiveGBs"


Description
       Text
       Tree
       Example
       CannedExample
     Acknowledgement
     Contributors
     References
     Caveat
     SeeAlso
     Subnodes

doc ///
     Key
     Headline
     Usage
       degreeMap phi
     Inputs
       phi: ...
     Outputs
     Consequences
       Item
     Description
       Text
       Example
       CannedExample
       Code
       Pre
     ExampleFiles
     Contributors
     References
     Caveat
     SeeAlso

     ///

