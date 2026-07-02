needsPackage "CyclicFlats"

cyclicFlatsofBases = method()
cyclicFlatsofBases List := B -> (
    MatroidofBases := matroid(B);
    flatsofMatroid := flats MatroidofBases;
    for flats in flatsofMatroid do (
        for i in flats do (
            --actually code this up
        )
    );
)