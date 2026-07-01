-*
E = set {1,2,3,4,5}
M = set {(set {},0),(set {1}, 1),(set {2}, 1),(set {3}, 1),(set {4}, 1),(set {5}, 1),(set {1,2}, 1), (set {1,5}, 2), (set {2,4}, 2), (set {2,5}, 2), (set {4,5}, 2)}
G = {set {}, set {1}, set {2}, set {3}, set {1,2}, set {1,2,3}, set {2,3}}
H = hashTable{(set {},0),(set {1},1), (set {2},1), (set {3},1), (set {1,2},2), (set {1,2,3},3), (set {2,3},2) }


for g in G do (
    for h in G do (
        print g;
        if isSubset(g,h) and g != h then
            if H#h - H#g == 0 or H#h - H#g >= #(h - g) then print "false" break
    )
)
*-
loadPackage "Posets"

areCyclicFlats = method()
areCyclicFlats List := l -> (
    H := hashTable l;
    G := keys H;
    P := poset(G, isSubset);
    --z0 checks if the poset is a lattice
    if not isLattice P then (
        return false)
    else (print "Z0 ok \n");
    --Z1
    if (( isMember(set {}, G)) and  (H#(set{}) == 0)) then (
        print "Z1 ok \n";
    )
    else (
        return false;
    );

    --Z2 check on principal filters but that's enough
    for g in G do (
        for h in principalFilter(P,g) do (
            if (g != h) then(  --maybe figure out a way around this, like just removing g from the principal filter
                if H#h - H#g == 0 or H#h - H#g >= #(h - g) then (
                    return false );
            )
        )
    );
    print "Z2 ok \n";
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
    print "Z3 ok";
)




M = {(set {},0),(set {1}, 1),(set {2}, 1),(set {3}, 1),(set {4}, 1),(set {5}, 1),(set {1,2}, 1), (set {1,5}, 2), (set {2,4}, 2), (set {2,5}, 2), (set {4,5}, 2)}
N = {(set {},0),(set {1},1),(set {2},1),(set {1,2},2)}
L = {(set {},0),(set {1,2},1),(set {3,4},1),(set {1,2,3,4},2)}
L2 = {(set {},0),(set {1,2},1),(set {2,3},1),(set {1,2,3},2)}

basesOfCyclicFlats = method()
basesOfCyclicFlats HashTable := H -> (
    G := keys H;
    topSet := union G;
    matroidRank := H#(topSet);
    bases := {};
    for x in subsets(topSet, matroidRank) do (
        tracker := false;
        for g in keys H do (
            tracker = false;
            intersectionSize := #(intersect(x,g));
            if intersectionSize > H#g then ( break );
            tracker = true;
        );
        if tracker then ( bases = append(bases, {x}) );
    );
    return bases;
)