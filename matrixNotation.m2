newPackage(
    "matrixNotation",
    Version => "0.1",
    Date => "",
    Headline => "A package for computing Comprehensive Groebner Bases (CGBs)",
    Authors => {
        { Name => "Lorenzo De Biase", Email => "lorenzo.debiase@enea.it", HomePage => "https://sites.google.com/view/lorenzodebiase/"},
        { Name => "Weijia Wang", Email => "weijia.wang@lip6.fr", HomePage => "https://weijia.perso.lip6.fr/"},
        { Name => "Angelo El Saliby", Email => "angelo.el.saliby@mis.mpg.de", HomePage => "angeloelsaliby.github.io"},
        { Name => "Oliver Clarke", Email => "oliver.clarke@durham.ac.uk", HomePage => "https://www.oliverclarkemath.com"},
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""},
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => "https://sites.google.com/view/mariaagustinacagliero/"},
        { Name => "Giulia Gaggero", Email => "gaggerog@mcmaster.ca", HomePage => ""},
        { Name => "Woody Cohen", Email => "2597103@swansea.ac.uk", HomePage => ""}
        },
    Keywords => {""},
    AuxiliaryFiles => false,
    PackageImports => {"MinimalPrimes","RealRoots"},
    DebuggingMode => true
    )

export {
    "CGBMain",
    "CGB",
    "cgbOnGraph",
    "ReduceStrata", 
    "CGBFromTriple", 
    "PGBMain", 
    "MDBasis",
    "Depth"
    } -- functions, objects to export

protect CGBMainTriples
protect Loops

-* Code section *-

CGBTriple = new Type of HashTable

protect coefficientsRing  --Probably needs to be changed
                          --b/c too similar to coefficientRing
protect totalRing
protect flattenedRing
protect triple            --Probably needs to be changed b/c 
                          --too generic?


ringOrder = method(); -- returns the monomial order of a polynomial ring
ringOrder PolynomialRing := List => R -> (
    order := select(toList (options R).MonomialOrder, orderEntry -> not member(first orderEntry, {MonomialSize, Position}));
    n := numgens R; 
    apply(order, orderEntry -> (
        if first orderEntry === Weights then (
            -- For U = QQ[a]; R = U[x,y,z, MonomialOrder => {Lex => 1, GLex}];
            -- {Lex => 1, GLex} unexpectedly expands to {Lex => 1, Weights => {1,1,1}, Lex => 2}.
            -- The bug is confirmed and will be fixed in future versions of Macaulay2: https://github.com/Macaulay2/M2/pull/4673
            -- Anyway, we ignore the unused weights as a hotfix for now.
            Weights => take(last orderEntry, min(n, #last orderEntry))
        ) else (
            n = n - if instance(last orderEntry, ZZ) then last orderEntry else #last orderEntry;
            orderEntry
        )
    ))
);

CGBFromTriple = method(); --Constructor for a CGBTriple starting from
                          --a list {E, F, G} where V(E)\V(F) is the 
                          --parametric strata and G is the set of 
                          --polynomial to be studied on it.

CGBFromTriple List := CGBTriple => (L) -> (
    if(length L == 3 and length L_0 > 0 and length L_2 > 0) then (
        R := ring L_2_0;
        return new CGBTriple from {
            "triple" => {matrix {L_0}, matrix {L_1}, matrix {L_2}},
            "cgbData" => CGBDataFromRings(R)};
        );
);

CGBDataFromRings = method();

CGBDataFromRings Ring := CGBData => (R) -> (
  X := gens R;
  KU := coefficientRing R;
  U := gens KU;
  K := coefficientRing KU;
  RExt := K[getSymbol "l", X, U, MonomialOrder => {Lex => 1} | ringOrder R | ringOrder KU];
  l := first gens RExt;
  RFlat := K[X, U, MonomialOrder => ringOrder R | ringOrder KU];
  RExt' := KU[l, X, MonomialOrder => {Lex => 1} | ringOrder R];
  RFlatl := RFlat[l];
  RtoRExt := map(RExt, R, drop(gens RExt, 1));
  RExttoRFlatl:= map(RFlatl,RExt, gens RFlatl | gens coefficientRing RFlatl);
  RExttoRExt':= map(RExt',RExt, gens RExt'| gens coefficientRing RExt');
  RExttoR:= map(R, RExt, {1} | gens R | gens coefficientRing R);
  RingsandThings := {R,X,RExt,RFlat,RExt',KU,RFlatl,RtoRExt,RExttoRFlatl,RExttoRExt',RExttoR};

  new CGBData from {
    "R"             => R,
    "X"             => X,
    "RExt"          => RExt,
    "RFlat"         => RFlat,
    "RExt'"         => RExt',
    "KU"            => KU,
    "RFlatl"        => RFlatl,
    "RtoRExt"       => RtoRExt,
    "RExttoRFlatl"  => RExttoRFlatl,
    "RExttoRExt'"   => RExttoRExt',
    "RExttoR"       => RExttoR
    }
);


listOfFactors = method() -- returns the list of factors of a ring element
listOfFactors (RingElement) := (h) -> (
  hfac := factor h;
  apply(#hfac, i -> if isConstant hfac#i#0 then 1_(ring h) else hfac#i#0)
);

squareFreePart = method() -- returns the square free part of a ring element
squareFreePart (RingElement) := (h) -> (
  R := ring h;
  f := product listOfFactors h;
  return f_R
);



isConsistent = method(); -- returns whether or not rad(E) intersect N is empty
isConsistent (List, List) := (E, N) -> (
  I := radical ideal E;
  any(N, p -> not isMember(p, I))
);

isConsistentRabinowitsch = method(); -- isConsistent, using the Rabinowitsch trick
isConsistentRabinowitsch (List, List) :=(E,N) -> (
    if isEmpty (E|N) then(return false);
    if isEmpty E then(
        if zero first N then error("Please remove zeros from N"); 
        return true;
        );
    if isEmpty N then(return false);
    R := ring E_0;
    S := (baseRing R)[Variables => 1+numgens R];
    M := map(S,R, (gens S)_{0..(numgens(R)-1)});
    any(N, f -> not isMember(1, ideal(apply(E,p->M(p))|{(M(f)*last(gens S)-1)})))
)
--R=QQ[x,y]
--E={x+y}
--N={y^2}
--isConsistentRabinowitsch(E,N)


diffLC = method(
    Options => {
        Strategy => "Rabinowitsch" -- "radical" or "Rabinowitsch"
    }
);
diffLC (Sequence, Sequence) := opts -> (A, B) -> (
  result := {(A#0 | {B#1}, A#1)} | apply(B#0, p -> (A#0, A#1 * p));
  if opts.Strategy == "radical" then (
    select(result, t -> isConsistent(t#0, {t#1}))
    ) 
  else if opts.Strategy == "Rabinowitsch" then (
    select(result, t -> isConsistentRabinowitsch(t#0, {t#1}))
    )
  else (
    error "Unknown strategy for diffLC"
  )
);

diffConstructibleByLC = method(
    Options => {
        Strategy => "radical"
        }
    );
diffConstructibleByLC (List, Sequence) := opts -> (C, LC) -> (
  flatten apply(C, t -> diffLC(t, LC, opts))
);


-- store all the maps and rings of a CGB computation in a object
CGBData = new Type of HashTable

CGBMain = method(
    Options => {
        ReduceStrata => false,
        Strategy => "Rabinowitsch",
        Verbose => false,
        Depth => -1
        }
    ); -- Initialises CGBMainRec

CGBMain (List) := o -> (F) -> (
  R := ring first F;
  S := first entries eliminateVariables F;
  CGBMain(F, S, o) | apply(S, s -> ({}, sub(s, R), {1_R}))
)
CGBMain (List, List) := o -> (F, S) -> (
  R := ring F_0;
  X := gens R;
  KU := coefficientRing R;
  U := gens KU;
  K := coefficientRing KU;
  RExt := K[getSymbol "l", X, U, MonomialOrder => {Lex => 1} | ringOrder R | ringOrder KU];
  l := first gens RExt;
  RFlat := K[X, U, MonomialOrder => ringOrder R | ringOrder KU];
  RExt' := KU[l, X, MonomialOrder => {Lex => 1} | ringOrder R];
  RFlatl := RFlat[l];
  RtoRExt := map(RExt, R, drop(gens RExt, 1));
  RExttoRFlatl:= map(RFlatl,RExt, gens RFlatl | gens coefficientRing RFlatl);
  RExttoRExt':= map(RExt',RExt, gens RExt'| gens coefficientRing RExt');
  RExttoR:= map(R, RExt, {1} | gens R | gens coefficientRing R);
  RingsandThings := {R,X,RExt,RFlat,RExt',KU,RFlatl,RtoRExt,RExttoRFlatl,RExttoRExt',RExttoR};

  cgbData := new CGBData from {
    "R"             => R,
    "X"             => X,
    "RExt"          => RExt,
    "RFlat"         => RFlat,
    "RExt'"         => RExt',
    "KU"            => KU,
    "RFlatl"        => RFlatl,
    "RtoRExt"       => RtoRExt,
    "RExttoRFlatl"  => RExttoRFlatl,
    "RExttoRExt'"   => RExttoRExt',
    "RExttoR"       => RExttoR
    };

  R = RingsandThings_0;
  X = RingsandThings_1;
  RExt = RingsandThings_2;
  RFlat = RingsandThings_3;
  RExt' = RingsandThings_4;
  KU = RingsandThings_5;
  RFlatl = RingsandThings_6;
  RtoRExt = RingsandThings_7;
  RExttoRFlatl = RingsandThings_8;
  RExttoRExt' = RingsandThings_9;
  RExttoR = RingsandThings_10;
  RingsandThings = {R,X,RExt,RFlat,RExt',KU,RFlatl,RtoRExt,RExttoRFlatl,RExttoRExt',RExttoR};
  CGBMainRec(F, S, {}, RingsandThings, o)
)

CGBMainRec = method(
    Options => {
        ReduceStrata => false,
        Strategy => "Rabinowitsch",
        Verbose => false,
        Depth => -1
        }
    );
CGBMainRec (List, List, List, List) := o -> (F, S, memo, RingsandThings) -> (
  R := RingsandThings_0;
  X := RingsandThings_1;
  RExt := RingsandThings_2;
  RFlat := RingsandThings_3;
  RExt' := RingsandThings_4;
  KU := RingsandThings_5;
  RFlatl := RingsandThings_6;
  RtoRExt := RingsandThings_7;
  RExttoRFlatl := RingsandThings_8;
  RExttoRExt' := RingsandThings_9;
  RExttoR := RingsandThings_10;
  if o.Verbose then (
      print("Computing CGB for F = " | toString F | " and S = " | toString S);
      );
  if 1 % (ideal S) == 0 then (
    return {}
  );
  l := first gens RExt;
  A := apply(F, i -> l * RtoRExt(i));
  B := apply(S, i -> (l-1) * RtoRExt(i));
  G := (entries gens gb(ideal join(A, B)))_0; -- isn't G in RExt? why do we substitute it in the line below? Let's clean it up without a sub

  pruneG := select(G, g -> (
          (first first exponents(leadMonomial sub(g,RExt))) > 0) and
      any(exponents(sub(leadCoefficient RExttoRFlatl(g),RFlat)), i -> any(i_(toList(0..(#(X)-1))), i -> i > 0)));
  pruneG = apply(pruneG, g -> leadCoefficient RExttoRExt'(g));
  h := lcm pruneG;
  for i in 0..(#(factor h)-1) do (
    if isConstant (factor h)#i#0 then(
         h = h//(factor h)#i#0;
         )
      );

  if o.ReduceStrata then (
      memo = memo | {
          (S, sub(h, R),
              for g in G list (
                  g' := RExttoR(g);
                  if zero g' then continue;
                  g')
              )
          };
      );

  if pruneG == {} then (
    if o.ReduceStrata then (
      return memo
    ) else (
      return {
          (S, sub(h, R),
              for g in G list (
                  g' := RExttoR(g);
                  if zero g' then continue;
                  g')
              )
          }
      )
  );

  -- H := pruneG; -- (takes too long to terminate if we do not factor h)
  -- H := unique apply(pruneG, g -> squareFreePart g); -- (takes a bit longer to terminate)

  if o.Depth == 0 then (
      -- TODO add a return statement for both ReduceStrata / non ReduceStrata

      );

  H := listOfFactors h;
  if o.ReduceStrata then (
      diffset := {};
      for hi in H do (
          diffset = {({sub(hi, KU)}, 1_(KU))};
          for t in memo do (
              diffset = diffConstructibleByLC(diffset, (apply(t#0, p -> sub(p, KU)), sub(t#1, KU)), Strategy => o.Strategy);
              if isEmpty diffset then (
                  break
                  );
              );
          if isEmpty diffset then (
              continue;
              );
          if o.Depth != 0 then (
              memo = CGBMainRec(F, append(S, sub(hi, R)), memo, RingsandThings, o ++ {Depth => o.Depth -1});
              )
          );
      return memo
      ) else (
      return {
          (S, sub(h, R),
              for g in G list (
                  g' := RExttoR(g);
                  if zero g' then continue;
                  g')
              )
          } | if o.Depth == 0 then {} else flatten apply(H, hi -> CGBMainRec(F, append(S, sub(hi, R)), memo, RingsandThings, o ++ {Depth => o.Depth -1}))
      );
  );


-*

Notes on Optimisation:

-- profiling - see what else is taking time

needsPackage "ComprehensiveGBs"
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
profile CGBMain(F, {});
profileSummary

*-

CGB=method( Options => {
        ReduceStrata => false,
        Strategy => "Rabinowitsch",
        Verbose => false,
        Depth => -1
        })
CGB(List):= o -> F->(
    s:=first entries eliminateVariables(F);
    result:=s;
    G:=CGBMain(F,s, ReduceStrata => o.ReduceStrata, Strategy => o.Strategy , Verbose => o.Verbose, Depth => o.Depth);
    for i in G do (
        result=result|(i_2);
        );
    
    unique result
)


eliminateVariables=method()
eliminateVariables(List):=F->(
    R:=ring first F;
    n:=numgens(R);
    C:=coefficientRing R;
    m:=numgens C;
    x:=getSymbol "x";
    u:=getSymbol "u";
    K:=coefficientRing C;
    S:=K[x_1..x_n,u_1..u_m, MonomialOrder => ringOrder R | ringOrder C];
    U:=gens C;
    X:=gens R;
    l1:=for i from 0 to m-1 list U_i=>S_(i+n);
    l2:=for j from 0 to n-1 list X_j=>S_j;
    F':=apply(F,h->sub(h,l1|l2));
    F'gbgens:=gens gb(ideal(F'));
    variableBlocks := select(ringOrder R, orderEntry -> first orderEntry =!= Weights);
    S':=selectInSubring(#variableBlocks,F'gbgens);
    mm:=map(C,ring S',
        toList(n:0)|gens C   
        );
    mm(S')
    )


cgbOnGraph=method()
cgbOnGraph(List,ZZ):=(G,d)->(
  V:=G_0;
  E:=G_1;
  x:=getSymbol "x";
  w:=getSymbol "w";
  S:=QQ[toSequence apply(E, l -> w_l)];
  R:=S[x_(V_0,1)..x_(V_(#V-1),d)];
  F:=for i in E list(sum(1..d,k->(R_(2*i_0+k-3)-R_(2*i_1+k-3))^2)-S_(position(E, j -> j === i)));
  (F, CGBMain(F, {}))
)

--Given two lists A and B return the list
--{a*b s.t. a in A and b in B}
totalListProduct = method();
totalListProduct (List, List) := (A, B) -> (
    if length A == 0 then (
      return B
    );
    if length B == 0 then (
      return A
    );
    return flatten(
        for a in A list(
            for b in B list (
                a*b
            )
        )
    )
);


--------------------------------------------------
-- Implementing definition 4.1 of 
-- "An efficient algorithm for computing a 
-- comprehensive Gröbner system of a parametric 
-- polynomial system", D. Kapur Y. Sun D. Wang, 
-- J. of Symbolic Computation issue 49, 2013
--------------------------------------------------
MDBasis = method();
MDBasis (List) := (G) -> (
    F := G;
    if length F == 0 then (
        return {}
        );
    Basis := {first F};
    F = delete(first F, F); 
    for g in F do ( --loop through elements of G
         --print("Deleting ", g, "from ", F);
         F = delete(g, F); 
         toAdd := true; --At the end of the loop, if LT_x(g) is not already implied 
                        --by elements in Basis, we should add g to our Basis
         for f in Basis do (
            --print(f, Basis);
            LTg := leadMonomial(g);
            LTf := leadMonomial(f);
            if LTg % LTf == 0 then (
                toAdd = false; --LTg is already in Basis, exit the loop and do not add g to Basis
                break
            )  
            else if LTf % LTg == 0 then ( --LTg divides something in Basis, so it can replace it
                --print("Deliting ", f, " from ", Basis, " and adding ", g );
                Basis = unique(delete(f, Basis) | {g});
                toAdd = false; --avoid adding g multiple times
                continue --might happen that LTg divides other leading terms in Basis
            );
         );
         if toAdd then ( -- LTg is not implied by anything in Basis
            Basis |=  {g};
         );
    );
    return Basis
);


--------------------------------------------------
--Implementing algorithm in section 4.1 of 
--"An efficient algorithm for computing a 
--comprehensive Gröbner system of a parametric 
--polynomial system", D.Kapur Y. Sun D. Wang, 
--J. of Symbolic Computation issue 49, 2013
--------------------------------------------------
PGBMain = method();
PGBMain (CGBTriple) := T -> (
    {E, N, F} := T#"triple";
    cgbData := T#"cgbData";
    R:=cgbData#"R";
    X:=cgbData#"X";
    RExt:=cgbData#"RExt"; 
    RFlat:=cgbData#"RFlat";
    RExt':=cgbData#"RExt'";
    KU:=cgbData#"KU";
    RFlatl:=cgbData#"RFlatl";
    RtoRExt:=cgbData#"RtoRExt";
    RExttoRFlatl:=cgbData#"RExttoRFlatl";
    RExttoRExt':=cgbData#"RExttoRExt'";
    RExttoR:=cgbData#"RExttoR";
    --print(E, length N);
    if not(consistencyCheckAllTogether(E, N)) then (
        return {} --The domain is empty
    );
    --Compute the GB of union(E, F), but viewing the parameters as variables
    G := first entries gens(gb (ideal(apply((E | F), e -> sub(e, RFlat)))));
    if member(sub(1, RFlat), G) then (
        return {{E, N, {promote(1, R)}}} --Trivial case where the vanishing set is empty
    );
    Gr := for g in G list ( --The polynomials in G that only contain the parameters
        l := lift(sub(g, R), KU, Verify =>false);
        --lift() with Verify=>false returns Null when the lift is not possible
        --i.e. when the polynomial contains something other than parametetrs
        if instance(l, Nothing) then (continue);
        l
    );
    -- By convention, an empty list for a GB means that the 
    -- corresponding vanishing set is the whole space, 
    -- which is equivalent to only containing the 0 element.
    -- To keep track of the original rings down the line and in the output, 
    -- we never return an empty GB.
    if length Gr == 0 then (
        Gr = {0_KU}; 
    );
    productList := unique(totalListProduct(Gr, N)); --The list obtained by multiplying every element in Gr with every element in N
    if length(productList) == 0 then (
        productList = {0_KU};
    );
    PGB := {};
    if consistencyCheckAllTogether (E, productList) then (
        PGB = {{E, productList, {1_R}}};
    );
    if not(consistencyCheckAllTogether(productList, N)) then (
        return PGB
    );
    --Elements of GB that do not only contain parameters
    listDiff := toList((new Set from apply(G, i->sub(i, R))) - (new Set from apply(Gr, i->sub(i, R))));
    Gm := MDBasis(listDiff);
    H := unique(apply(Gm, g->squareFreePart(leadCoefficient(sub(g, R)))));
    h := squareFreePart(lcm(H));
    productList = unique(apply(totalListProduct(N, {sub(h, KU)}), i -> squareFreePart(i)));
    if consistencyCheckAllTogether(Gr, productList) then (
        PGB = unique(PGB | {{Gr, productList, Gm}});
    );

    for i in 0..(length(H)-1) do (
        if i == 0 then (
            PGB = unique(PGB | PGBMain(CGBFromTriple({
            unique(Gr | {H_i}), 
            N, 
            listDiff}
            )))
        ) else (
        PGB = unique(PGB | PGBMain(CGBFromTriple({
            unique(Gr | {H_i}), 
            unique(totalListProduct(N, {squareFreePart(product(H_{0..(i-1)}))})), 
            listDiff}
        ))));
    );

    return PGB  
);

PGBMain List := F -> (
    if #F == 0 then error("List must be non-empty");
    R := ring first F;
    U := coefficientRing R;
    PGBMain(CGBFromTriple({{0_U}, {1_U}, F}))
    )



-----------------------------
--zeroDimCheck if for those
--cases in which <E> is
--zero dimensional.
--It uses RealRoots.
-----------------------------

zeroDimCheck = method();
zeroDimCheck (List, RingElement) := (E, f) -> (
    I := ideal E;
    pf := characteristicPolynomial(f, I);
    d := first degree pf;
    lambda := first gens ring pf;
    if pf == lambda^d then
        false --inconsistent
    else
        true --consistent
);

-----------------------------
--CCheck if for those
--cases in which <E> is
--of positive dimensional.
-----------------------------

CCheck = method();
CCheck (List, RingElement) := (E, f) -> (
    R := ring f;
    U := gens R;
    supports := apply(E, g -> (
        --if g == 0 then (return 0_R);
        e := first exponents(leadMonomial g);
        select(0..(#e-1), i -> e_i != 0)
    ));

    V := {};

    for i from 0 to (#U - 1) do (
        candidate := V | {i};

        if not any(supports, S -> all(S, j -> member(j, candidate))) then (
            V = candidate;
        );
    );
    alpha := apply(numgens R, i -> random(-100,100));


    -*
    remaining := select(0..(#U-1), i -> not member(i,V));

    newR := coefficientRing R[apply(remaining, i -> U_i)]; --
    newU := gens newR;

    images := toList  apply(0..(#U-1), i -> (
        if member(i,V) then (
            alpha_(position(V, j -> j == i))
        ) else (
            newU_(position(remaining, j -> j == i))
        )
    ));
    *-

    phi := map(R,R,for i from 0 to numgens R-1 list if member(i, V) then alpha_i else R_i);

    spE := gb (ideal apply(E, g -> phi(g)) + ideal(for i in V list R_i));
    -- the above is a little different from KSW where they restrict to a smaller ring
    -- and check that spE is zero dimensional there
    -- Here we add in the variables in order to avoid constructing a new polynomial ring
    -- and hopefully the GB computation is just as fast

    fAlpha := phi(f);
    -- fAlpha = sub(fAlpha, newR); -- shouldn't need this
    GspE := flatten entries gens spE;

    if dim( ideal(GspE)) == 0 and zeroDimCheck(GspE, fAlpha) then (
        return true; -- certifies consistency
    );
    return false -- unknown consistency (i.e., it could still be consistent)
  
);



ICheck = method(
    Options => {
        Loops => 5
    }
);

ICheck (List, RingElement) := o -> (E, f) -> (
    p := f;
    H:= gens gb ideal E;
    for i from 1 to o.Loops do (
        s := 0;
        for m in terms p do (
            s = s + (p*m) % H; --H stores the computed Groebner basis, so it is not computed twice
        );
        if s == 0 then (
            return true; -- certifies inconsistency
        );
        p = s;
    );

    return false; -- unknown consistency
);

----------------------------------------
--THE FOLLOWING PUTS TOGETHER ZERODIMCHECK
--CCHECK AND ICHECK
--1)check whether f is already in <E>
--2)determine the dimension of <E>
--3) zeroDimCheck or CCheck
--4) if CCheck is not enough, do ICheck
----------------------------------------

consistencyCheckAllTogether = method(
    Options => {
        Loops => 5
    }
);

consistencyCheckAllTogether (Thing, RingElement) := o -> (E, f) -> (
    if (f % ideal E) == 0 then (
        print "true: direct ideal membership check was used";
        return false; -- inconsistent
    );

    d := dim ideal E;

    if d == 0 then (
        print "zeroDimCheck was used";
        return zeroDimCheck(E,f);
    );

    if CCheck(E,f) then (
        print "false: CCheck was used";
        return true; -- consistent
    );

    if ICheck(E,f, Loops => o.Loops) then (
        print "true: ICheck was used";
        return false; -- inconsistent
    );

    print "General check was used";
    return null; -- temporary
);

-- Cannot have ideal E = (0) or ideal F = (0)
consistencyCheckAllTogether (Matrix, Matrix) := o -> (E, N) -> (
    if numColumns E == 0 then (
      if numColumns N == 0 then (
        return false
      );
    ) else (
      KU := ring E;
      if ideal E == ideal(0_KU) or ideal N == ideal(0_KU) then (
        if ideal N == ideal(0_KU) then return false;
        return true);
    );
    for f in N do (
        check := consistencyCheckAllTogether(E, f, Loops => o.Loops);

        if check === false then (
            return false;
        );

        if instance(check, Nothing) then (
            return isConsistentRabinowitsch(E, N);
        );
    );

    return true
);


