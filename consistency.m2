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
    R = ring F_0;
    CoeffRing = ring E_0;
    G := new Set from (gens(gb(apply((E | N), e -> promote(e, R)))));
    if member(promote(1, R), G) then (
        return {E, N, {promote(1, R)}}
    );
    Gr := for g in G list (
        l := lift(g, CoeffRing, Verify =>false);
        if instance(l, Nothing) then (continue);
        l
    ); 
    productList = product(Gr, N, (a, b) -> a*promote(b, R));
    if not(consistent(E, productList)) then (
        PGB := {};
    ) else (
        PGB := {{E, productList, {1}}};
    )
);