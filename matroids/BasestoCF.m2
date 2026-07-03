needsPackage "CyclicFlats"
needsPackage "Matroids"

cyclicFlatsofBases = method()
cyclicFlatsofBases List := B -> (
    E = toList (union B);

    M := matroid(E, B);
    flatsofMatroid := flats(M);
    cyclicFlat := {};
    
    for flat in flatsofMatroid do (
        t := true;
        for i in toList(flat) do (
            flati = flat - set {i};
            if not (rank(M, flati) == rank(M, flat)) then (
                t = false;
                break;
            );
          
        );
        if t then (
            cyclicFlat = append(cyclicFlat, {flat});
        )
    );
    return cyclicFlat;
)

B = {set {1,2}, set {3,4}, set {1,4}, set {2,3}, set {1,3}, set {2,4}}
