loadPackage "Posets";

breakshittogether = {(set {},0),(set {1,2},1), (set {2,3},1), (set {1,2,3},2)}

z3CyclicFlats = method()
z3CyclicFlats List := l -> (
    H := hashTable l;
    G := keys H;
    P := poset(G, isSubset);
    --Z0
    if isLattice P then ( print "Z0 passed"; ) else (return false);
    --Z1
    --Z3
    for g in G do (
        for h in G do (
          
            rankSum = H#g + H#h;

            pJoin = (posetJoin(P, g, h))#0;
    
            pMeet = (posetMeet(P, g, h))#0;

            rankJoin = H#(pJoin);
            
            rankMeet = H#(pMeet);

            if ( rankSum < rankJoin + rankMeet + #(intersect(g,h)) - #(pMeet)) then (return false)
        );
    );
    print "Z3 passed";


    
    
    return true;
)