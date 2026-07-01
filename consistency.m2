consistent = method();
consistent (List, List) := (E, N) ->(
    I := radical (ideal E);
    return not(isEmpty(select(N, n -> isMember(n, I))))
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
PGBMain (List, List, List) := (E, N, F) -> (
    if not(consistent(E, N)) then (
        return {}
    );
    R := ring F_0;
    RFlat = QQ[ gens R, gens (coefficientRing R), MonomialOrder => Lex];
    CoeffRing = ring E_0;
    G := first entries gens(gb (ideal(apply((E | N), e -> sub(e, RFlat)))));
    if member(sub(1, RFlat), G) then (
        return {E, N, {promote(1, R)}}
    );
    Gr := for g in G list (
        l := lift(g, CoeffRing, Verify =>false);
        if instance(l, Nothing) then (continue);
        promote(l, R)
    ); 
    productList = totalListProduct(Gr, N);
    product(Gr, N, (a, b) -> a*promote(b, R));
    PGB := {};
    if consistent(E, productList) then (
        PGB := {{E, productList, {1}}};
    );
    if not(consistent(productList, N)) then (
        return PGB
    );
    diff = (new Set from G) - (new Set from Gr);
    Gm := MDBasis(new List from diff);
    H := apply(Gm, g->leadMonomial(sub(g, R)));
    h := lcm(H);
    productList = totalListProduct(N, {h});
    if consistent(Gr, productList) then (
        PGB = PGB | {Gr, productList, Gm};
    );
    for i in 0..(length(H)-1) do (
        PGB = PGB | PGBMain(Gr | {H_i}, totalListProduct(N, H_{0..i}), diff);
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
            print(LTg, LTf);
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

---------------------
--TEST
---------------------
--R = QQ[a,b,c][x,y,z, MonomialOrder => Lex];
--G = {a*x*y + b*x, b*x^2*y+c*z, a*b*x+a*x*y+z, a*y+z, c*x + c*z^2}
--assert({a*y + z, c*x + c*z^2} == MDBasis(G));
