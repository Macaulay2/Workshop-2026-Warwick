--profile method() ---->> Gives a count of called functions and elapsed time


CGBTriple = new Type of MutableHashTable

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


-- Ollie: for the consistency test, we don't need to compute radical of E
-- we can use Rabinowitsch to just get away with one GB computation!
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

PGBMain = method();
PGBMain (CGBTriple) := T -> (
    {E, N, F} := T#triple;
    print(E, length N);
    if not(consistent(E, N)) then (
        return {}
    );
    R := T#totalRing;
    RFlat = T#flattenedRing;
    CoeffRing = T#coefficientsRing;
    G := first entries gens(gb (ideal(apply((E | F), e -> sub(e, RFlat)))));
    if member(sub(1, RFlat), G) then (
        return {{E, N, {promote(1, R)}}}
    );
    Gr := for g in G list (
        l := lift(sub(g, R), CoeffRing, Verify =>false);
        if instance(l, Nothing) then (continue);
        l
    );
    if length Gr == 0 then (
        Gr = {0_U};
    );
    productList = totalListProduct(Gr, N);
    if length(productList) == 0 then (
        productList = {0_CoeffRing};
    );
    PGB := {};
    if consistent(E, productList) then (
        PGB = {{E, productList, {1_R}}};
    );
    if not(consistent(productList, N)) then (
        return PGB
    );
    listDiff := apply(toList((new Set from G) - (new Set from Gr)), l -> sub(l, R));
    Gm := MDBasis(listDiff);
    H := apply(Gm, g->leadCoefficient(sub(g, R)));
    h := lcm(H);
    productList = totalListProduct(N, {sub(h, CoeffRing)});
    if consistent(Gr, productList) then (
        PGB = PGB | {{Gr, productList, Gm}};
    );
    breakpoint
    for i in 0..(length(H)-1) do (
        PGB = PGB | PGBMain(CGBFromTriple({Gr | {H_i}, totalListProduct(N, {product(H_{0..(i-1)})}), listDiff}));
        );

    return PGB  
);

MDBasis = method();
MDBasis (List) := (G) -> (
    F := G;
    Basis := {first F};
    F = delete(first F, F);
    for g in F do (
         F = delete(g, F);
         for f in Basis do (
            LTg := leadMonomial(g);
            LTf := leadMonomial(f);
            if LTg % LTf == 0 then (
                break
            );  
            if LTf % LTg == 0 then (
                Basis = delete(f, Basis) | {g};
                continue
            );
            Basis = Basis | {g};
         ); 
    );

    return Basis 
);

end 
restart
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
U = QQ[a,b]
R = U[x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
T = CGBFromTriple({{0_U}, {1_U}, F})
L =PGBMain(T)

U = QQ[a,b]
R = U[x,y, MonomialOrder => Lex]
F = {a*x + b*y}
T = CGBFromTriple({{0_U}, {1_U}, F})
L =PGBMain(T)