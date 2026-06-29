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

areCyclicFlats = method()
areCyclicFlats Boolean := l -> (
    H = hashTable l;
    G = keys H;
    P = poset(G, isSubset);
    --Z0
    if not isLattice P then return false
    --Z1
    --Z2
    for g in G do (
        for h in G do (
            print g;
            if isSubset(g,h) and g != h then
                if H#h - H#g == 0 or H#h - H#g >= #(h - g) then return false
        )
    )
    --Z3
    
)