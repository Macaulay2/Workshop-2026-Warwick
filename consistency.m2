consistent = method();
consistent (List, List) := (E, N) ->(
    I := radical (ideal E);
    return not(isEmpty(select(N, n -> isMember(n, I))))
);

PGBMain = method();

PGBMain (List, List, List) := (E, N, F) -> (
    if not(consistent(E, N)) then (
        return {}
    );
    R := ring F_0;
    CoeffRing = ring E_0;
    G := first entries gens(gb (ideal(apply((E | N), e -> promote(e, R)))));
    if member(promote(1, R), G) then (
        return {E, N, {promote(1, R)}}
    );
    Gr := for g in G list (
        l := lift(g, CoeffRing, Verify =>false);
        if instance(l, Nothing) then (continue);
        promote(l, R)
    ); 
    productList =flatten ( for g in Gr list (
        for n in N list (
            n*g
            )
        ));
    product(Gr, N, (a, b) -> a*promote(b, R));
    if not(consistent(E, productList)) then (
        PGB := {};
    ) else (
        PGB := {{E, productList, {1}}};
    );
    if not(consistent(productList, N)) then (
        return PGB
    );
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

TEST ///