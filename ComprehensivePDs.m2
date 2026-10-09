
hasConstant = method();
hasConstant (Ideal) := I -> (
    R = ring I;
    isMember()
);

irredFeadisibleCPDS = method();

irredFeadisibleCPDS (List, List) := (gI, H) -> (
    I = ideal gI;
    R = ring I;
    X = gens R;
    if isMember(1, I) or isMember(1, I + ideal H) then return {}; -- first check might me superflous in this case
    CPDS = {};
    Q = primaryDecomposition(I + H);
    groundIdeal = radical(eliminateVariables(X, I + H);
    Q' = select(Q, (
        q -> (
            radical(eliminateVariables(X, q)) == groundIdeal)
        )
    ))
); 

strataFromPD = method();

strataFromFilteredPD (List, List) := (gI, Q) -> (
    I := ideal gI;
    R := ring I;
    F := QQ[t_1..t_((length Q)-1), gens R, gens coefficientRing R];
    T := (gens F)_{0..((length Q)-2)};
    H := sum(apply(Q / (q -> sub(q, F)), T | {1-sum(T)}, (q,t) -> q*t))
    G := gens gb H;
    needsPackage "ComprehensiveGBs";
    J := CGBMain(G, , Depth => 0);
);