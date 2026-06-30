debugLevel = 1;
matroid = method(Options => {EntryMode => "bases", ParallelEdges => {}, Loops => {}})
isFlat = method()
isFlat List := Flat -> (
    if #Flat !== 2 then (
        if debugLevel > 0 then printerr("Error: " | toString(Flat) | " has length " | toString(#Flat) | ", should be 2.");
        return false;
    )
    if not instance(Flat#0, Set) then (
        if debugLevel > 0 then printerr("Error: " | toString(Flat#0) | " is not a set.");
        return false;
    );

    if not instance(Flat#1, ZZ) then (
        if debugLevel > 0 then printerr("Error: " | toString(Flat#1) | " is not an integer.");
        return false;
    );
    return true;
);

isCyclicFlats = method()
isCyclicFlats = List := cFlats -> (
    areFlats = apply(cFlats, isFlat);
    if member(false, areFlats) then (
        if debugLevel > 0 then printerr("Error: " | toString(cFlats) | " contains at least one non-flat.");
        return false;
    );
    return true;
);
