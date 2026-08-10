--profile method() ---->> Gives a count of called functions and elapsed time


CGBTriple = new Type of HashTable

protect coefficientsRing
protect totalRing
protect flattenedRing
protect triple

CGBFromTriple = method();
CGBFromTriple List := CGB => (L) -> (
    if(length L == 3 and length L_0 > 0 and length L_2 > 0) then (
        R := ring L_2_0;
        coeff := coefficientRing R;
        scalarRing = coefficientRing coeff;
        return new CGBTriple from {triple => L, coefficientsRing => coeff, totalRing => R , flattenedRing => scalarRing[gens R, gens coeff, MonomialOrder => Lex] };
        );
);
getCoefficientsRing = method();

getCoefficientsRing = method();

isConsistentRabinowitsch = method();
isConsistentRabinowitsch (List, List) :=(E,N) -> (
    if isEmpty (E|N) then(return false);
    if isEmpty E then(return set(N) != 0);
    if isEmpty N then(return false);
    R := ring E_0;
    S := (baseRing R)[Variables => 1+numgens R];
    M := map(S,R, (gens S)_{0..(numgens(R)-1)});
    any(N, f -> not isMember(1, ideal(apply(E,p->M(p))|{(M(f)*last(gens S)-1)})))
)

-- Ollie: for the consistency test, we don't need to compute radical of E
-- we can use Rabinowitsch to just get away with one GB computation!

listOfFactors = method()
listOfFactors := (h) -> (
  hfac := factor h;
  apply(#hfac, i -> if isConstant hfac#i#0 then 1_(ring h) else hfac#i#0)
)

squareFreePart = method()
squareFreePart  := (h) -> (
  product listOfFactors h
)


totalListProduct = method();
totalListProduct (List, List) := (A, B) -> (
    return flatten(
        for a in A list(
            for b in B list (
                a*b
            )
        )
    )
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
    {E, N, F} := T#triple;
    --print(E, length N);
    if not(isConsistentRabinowitsch(E, N)) then (
        return {} --The domain is empty
    );
    R := T#totalRing; --Ring with parameters and variables
    RFlat = T#flattenedRing; --Ring where parameters are consdiered variables
    CoeffRing = T#coefficientsRing; -- Ring with only parameters
    --Compute the GB of union(E, F), but viewing the parameters as variables
    G := first entries gens(gb (ideal(apply((E | F), e -> sub(e, RFlat)))));
    if member(sub(1, RFlat), G) then (
        return {{E, N, {promote(1, R)}}} --Trivial case where the vanishing set is empty
    );
    Gr := for g in G list ( --The polynomials in G that only contain the parameters
        l := lift(sub(g, R), CoeffRing, Verify =>false);
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
        Gr = {0_U}; 
    );
    productList := unique(totalListProduct(Gr, N)); --The list obtained by multiplying every element in Gr with every element in N
    if length(productList) == 0 then (
        productList = {0_CoeffRing};
    );
    PGB := {};
    if isConsistentRabinowitsch(E, productList) then (
        PGB = {{E, productList, {1_R}}};
    );
    if not(isConsistentRabinowitsch(productList, N)) then (
        return PGB
    );
    listDiff := toList((new Set from apply(G, i->sub(i, R))) - (new Set from apply(Gr, i->sub(i, R))));
    
    ------------------------------------------------------
    --THIS IS MY PERSONAL INTERPRETATION!
    if length listDiff == 0 then (
        breakpoint
        return {}
    );
    ----------------------------------------
    Gm := MDBasis(listDiff);
    H := unique(apply(Gm, g->squareFreePart(leadCoefficient(sub(g, R)))));
    h := squareFreePart(lcm(H));
    productList = unique(apply(totalListProduct(N, {sub(h, CoeffRing)}), i -> squareFreePart(i)));
    if isConsistentRabinowitsch(Gr, productList) then (
        PGB = unique(PGB | {{Gr, productList, Gm}});
    );
    --breakpoint
    for i in 0..(length(H)-1) do (
        if i == 0 then (
            PGB = unique(PGB | PGBMain(CGBFromTriple({
            unique(Gr | {H_i}), 
            N, 
            listDiff}
            )))
        ) else (
        PGB = unique(PGB | PGBMain(CGBFromTriple({
            unique(Gr | {H_i}), 
            unique(totalListProduct(N, {squareFreePart(product(H_{0..(i-1)}))})), 
            listDiff}
        ))));
    );

    return PGB  
);

MDBasis = method();
MDBasis (List) := (G) -> (
    F := G;
    Basis := {first F};
    F = delete(first F, F);
    for g in F do (
         print("Deleting ", g, "from ", F);
         F = delete(g, F);
         toAdd := true;
         for f in Basis do (
            print(f, Basis);
            LTg := leadMonomial(g);
            LTf := leadMonomial(f);
            if LTg % LTf == 0 then (
                toAdd = false;
                break
            )  
            else if LTf % LTg == 0 then (
                print("Deliting ", f, " from ", Basis, " and adding ", g );
                Basis = unique(delete(f, Basis) | {g});
                toAdd = false;
                continue
            );
         );
         if toAdd then (
            Basis |=  {g};
         );
    );
    return Basis 
);
-----------------------------
--TEST for MDBasis
-----------------------------
TEST /// -* Testing MDBasis on {a*x^2 − y, a*y^2 − 1, a*x − 1, (a + 1)*x − y, (a + 1)*y − a} *-
U = U = QQ[a, MonomialOrder => Lex];
R = U[x, y, MonomialOrder => Lex];
G = {a*x^2 - y, a*y^2 - 1, a*x - 1, (a + 1)*x - y, (a + 1)*y - a}
MDBasis(G)
///

end 
restart
installPackage "ComprehensiveGBs"
load "consistency.m2"
---------------------
--TEST
---------------------
U = QQ[a, b, c, MonomialOrder => Lex]
R = U[x,y,z, MonomialOrder => Lex];
G = {a*x*y + b*x, b*x^2*y+c*z, a*b*x+a*x*y+z, a*y+z, c*x + c*z^2}
T = CGBFromTriple({{0_U}, {1_U}, G})
L= PGBMain(T)
assert({a*y + z, c*x + c*z^2} == MDBasis(G));

--Example 9
U = QQ[a, b, c, MonomialOrder => Lex]
R = U[x,y,z, MonomialOrder => Lex];
F = {x^3 - a, y^4 - b, x+y-z}
T = CGBFromTriple({{0_U}, {1_U}, F})
L= PGBMain(T)

U = QQ[a,b]
R = U[x,y, MonomialOrder => Lex]
F = {a*x + b*y}
T = CGBFromTriple({{0_U}, {1_U}, F})
L =PGBMain(T)


consistent = method();
consistent (List, List) := (E, N) ->(
    if length E == 0 then (
        if length N == 0 then (
            return false
        );
        R := ring N_0;
        I := ideal 0_R;
    ) else (
        I := radical (ideal E);
    );
    
    return not(isEmpty(select(N, n -> not(isMember(n, I)))))
);