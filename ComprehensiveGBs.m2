newPackage(
    "ComprehensiveGBs",
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
            -- {Lex => 1, GLex} unexpectedly expands to {Lex => 1, Weights => {1,1,1}, Lex => 2}. Is that a bug?
            -- Anyway, we ignore the unused weights as a hacky fix.
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

CGBFromTriple List := CGB => (L) -> (
    if(length L == 3 and length L_0 > 0 and length L_2 > 0) then (
        R := ring L_2_0;
        coeff := coefficientRing R;
        scalarRing := coefficientRing coeff;
        return new CGBTriple from {
            triple => L,
            coefficientsRing => coeff,
            totalRing => R ,
            flattenedRing => scalarRing(monoid[gens R, gens coeff, MonomialOrder => ringOrder R | ringOrder coeff])};
        );
);


listOfFactors = method() -- returns the list of factors of a ring element
listOfFactors (RingElement) := (h) -> (
  hfac := factor h;
  apply(#hfac, i -> if isConstant hfac#i#0 then 1_(ring h) else hfac#i#0)
);

squareFreePart = method() -- returns the square free part of a ring element
squareFreePart (RingElement) := (h) -> (
  product listOfFactors h
);

squareFreePart (ZZ) := (h) -> (
  1
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
  CGBMain(F,{},o)
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
    {E, N, F} := T#triple;
    --print(E, length N);
    if not(isConsistentRabinowitsch(E, N)) then (
        return {} --The domain is empty
    );
    R := T#totalRing; --Ring with parameters and variables
    RFlat := T#flattenedRing; --Ring where parameters are consdiered variables
    CoeffRing := T#coefficientsRing; -- Ring with only parameters
    --Compute the GB of union(E, F), but viewing the parameters as variables
    G := first entries gens(gb (ideal(apply((E | F), e -> sub(e, RFlat)))));
    if member(sub(1, RFlat), G) then (
        return {{E, N, {promote(1, R)}}} --Trivial case where the vanishing set is empty
    );
    Gr := for g in G list ( --The polynomials in G that only contain the parameters
        l := lift(sub(g, R), CoeffRing, Verify =>false);
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
        Gr = {0_CoeffRing}; 
    );
    productList := unique(totalListProduct(Gr, N)); --The list obtained by multiplying every element in Gr with every element in N
    if length(productList) == 0 then (
        productList = {0_CoeffRing};
    );
    PGB := {};
    if isConsistentRabinowitsch(E, productList) then (
        PGB = {{E, productList, {1_R}}};
    );
    if not(isConsistentRabinowitsch(productList, N)) then (
        return PGB
    );
    --Elements of GB that do not only contain parameters
    listDiff := toList((new Set from apply(G, i->sub(i, R))) - (new Set from apply(Gr, i->sub(i, R))));
    Gm := MDBasis(listDiff);
    H := unique(apply(Gm, g->squareFreePart(leadCoefficient(sub(g, R)))));
    h := squareFreePart(lcm(H));
    if h == 1 then h = 1_CoeffRing;
    productList = unique(apply(totalListProduct(N, {sub(h, CoeffRing)}), i -> squareFreePart(i)));
    if isConsistentRabinowitsch(Gr, productList) then (
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

    if zeroDimCheck(GspE, fAlpha) then (
        return true; -- certifies consistency
    );
    return false -- unknown consistency (i.e., it could still be consistent)
  
);



ICheck = method(
    Options => {
        Loops => 5
        }
    )
ICheck (List, RingElement) := (E, f) -> (

    )




-* Documentation section *-

beginDocumentation()

doc ///
  Key
    ComprehensiveGBs
  Headline
    a package for computing Comprehensive Groebner Bases (CGBs).
  Description
    Text
    This package provides the implementations of two differnt algorithms for computing a comprehensive Gr\"obner system and a comprehensive Gr\"obner basis of a parametric ideal. 
    For a definition see Definition 2 of @HREF("#ref2","[2]")@ and Definition 2.1 of @HREF("ref2","[2]")@

    The function @TO "CBGMain"@ is the implementation of Algorithm CGBMain of @HREF("#ref2","[2]")@.

    Instead the function @TO "PGBMain"@ corresponds to the Algorithm PGBMain of @HREF("ref1","[2]")@.
      
  References
    @LABEL("[2]","id" => "ref2")@ Akira Suzuki and Yosuke Sato. 2006. A simple algorithm to compute comprehensive Gröbner bases using Gröbner bases. In Proceedings of the 2006 international symposium on Symbolic and algebraic computation (ISSAC '06). Association for Computing Machinery, New York, NY, USA, 326–331. https://doi.org/10.1145/1145768.1145821
    @LABEL("[1]","id" => "ref1")@ Deepak Kapur, Yao Sun, and Dingkang Wang. 2013. An efficient algorithm for computing a comprehensive Gr\"obner system of a parametric polynomial system. In Journal of Symbolic Computation, 49, 27-44.
///



doc ///
  Key
    "OlliesDocPage"
  Headline
    A small example
  Description
    Text 
      Description of the page you can insert some code snippets too:
      Here is a ring $R = \QQ[a,b][x,y]$ with a Lex monomial order ..
    Example
      R = QQ[a,b][x,y, MonomialOrder => Lex]
      F = {a*x + b*y}
      CGBMain(F, {})
    Text
      Amazing!
      A link to the package: @TO "ComprehensiveGBs"@.
      Sometimes we talk about @TT "true"@ things.
      
  SeeAlso
    ComprehensiveGBs
///

doc ///
  Key
    CGBMain
    (CGBMain, List, List)
    (CGBMain, List)
  Headline
    a method that computes a Comprehensive Groebner System
  Usage
    CGBMain(F,S)
    CGBMain(F)
  Inputs
    F :List
      of polynomials of a ring $R = k[U][X]$
    S :List
      of polynomials of a ring $RU = k[U]$
    ReduceStrata=>Boolean
    Strategy=>String
    Verbose=>Boolean
  Outputs
    G :List
      of Sequences of the form (E,N,G), where G is a Groebner basis on the set $V(E)\setminus V(N)$
  Description
    Text
      Implementation of the Algorithm proposed by Suzuki and Sato. Given a tower polynomial ring $R = k[U][X]$ for $U$ a set of parameters and $X$ a set of variables, $F\subset R$ an ideal of variables and parameters, and $S\subset k[U]$ an ideal satisfying $V(S)\subseteq V(\langle F\rangle\cap k[U])$, CGBMain takes $F$ and $S$ as inputs and returns a comprehensive Groebner system.
      The function itself passes $F$ and $S$ to CGBMainRec after initialising various objects.
      As above, the ring must be initialised as a tower ring:
    Example
      R1 = QQ[a,b][x,y]
    Text
      Here $X = \{x,y\}$ and $U = \{a,b\}$. If we wanted to find a comprehensive Groebner system over $\mathb{Q}^2$ for $F = \langle ax+by\rangle$, we input the following:
    Example
      F1 = {a*x+b*y};
      S1 = {};
      CGBMain(F1,S1)
-*
    Text
      CGBMain has several options: ReduceStrata, Strategy, and Verbose. ReduceStrata is an option to ignore computations on strata which have already been considered. This value is set to false by default. For smaller examples, changing this to true can reduce computation times, as for the following example. It will also give more easily parseable results.
    Example
      R2 = QQ[a,b][x,y,z];
      F2 = {x^2-a,y^3-b,x+y-z};
      S2 = {};
    Text
      The value is false by default as this is not true in general - for the example below (which will not be computed to save time, though the reader may verify if they desire) the option being false has an execution time of less than a minute. Setting ReduceStrata to true increases this execution time significantly (a rough estimate for time has not been found, as the computation takes so long).
    Example
      R3 = QQ[a,b][x,y,z,s, MonomialOrder => Lex];
      f=(x-a)^2+b*y^2+b;
      F3 = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
    Text
      Strategy is an option that depends on ReduceStrata, and has two valid inputs, being "radical" and "Rabinowitsch" - other inputs will return an error. The former reduces strata by directly computing radicals of ideals, and the latter utilises the Rabinowitsch trick. The latter is, in general, considerably faster.
      Setting Verbose to True will print whatever $F$ and $S$ that CGBMainRec is currently working on:
    Example
      CGBMain(F1,S1,Verbose=>true)
*-
    Text
      CGBMain can take in one or two lists as inputs - when $S$ is not specified, the function will assume S = {}.
  SeeAlso
    CGB
    ReduceStrata
    Strategy
    Verbose
    Depth
  ///

doc ///
  Key
    ReduceStrata
  Headline
    ignore computations on strata which have already been considered
  Description
    Text
      ReduceStrata is an option to ignore computations on strata which have already been considered. This value is set to false by default. For smaller examples, changing this to true can reduce computation times, as for the following example. It will also give more easily parseable results.
    Example
      R2 = QQ[a,b][x,y,z];
      F2 = {x^2-a,y^3-b,x+y-z};
      S2 = {};
    Text
      The value is false by default as this is not true in general - for the example below (which will not be computed to save time, though the reader may verify if they desire) the option being false has an execution time of less than a minute. Setting ReduceStrata to true increases this execution time significantly (a rough estimate for time has not been found, as the computation takes so long).
    Example
      R3 = QQ[a,b][x,y,z,s, MonomialOrder => Lex];
      f=(x-a)^2+b*y^2+b;
      F3 = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
  SeeAlso
    CGBMain
///

doc ///
  Key
    Strategy
  Headline
    how to compute the radical in @TO "ReduceStrata"@
  Description
    Text
      Strategy is an option that depends on @TO "ReduceStrata"@. It is for cheking if a pair $(E,N) \subseteq k[U]$ is consistent, i.e., if $V(E)\backslash V(N)$ is not empty. In order to do that the radical of ideal(E) has to be computed, see Section 5 of @HREF("ref1","1")@ for details.
      Strategy has two valid inputs, being "radical" and "Rabinowitsch" - other inputs will return an error. The former reduces strata by directly computing radicals of ideals, and the latter utilises the Rabinowitsch trick. The latter is, in general, considerably faster.
  References
    @LABEL("[1]","id" => "ref1")@ Deepak Kapur, Yao Sun, and Dingkang Wang. 2013. An efficient algorithm for computing a comprehensive Gr\"obner system of a parametric polynomial system. In Journal of Symbolic Computation, 49, 27-44.
  SeeAlso
    CGBMain
    ReduceStrata
///

doc ///
  Key
    Verbose
  Headline
    a record of CGBMain iterations 
  Description
    Text
      Setting Verbose to True will print whatever $F$ and $S$ that CGBMainRec is currently working on:
    Example
      CGBMain(F1,S1,Verbose=>true)
  SeeAlso
    CGBMain
///


doc ///
  Key
    Depth
  Headline
    not sure of what it is 
  Description
   
  SeeAlso
    CGBMain    
///
  
doc ///
  Key
    cgbOnGraph
    (cgbOnGraph,List,ZZ)
  Headline
    A method for creating parametrised polynomial systems from a graph and calculating a Comprehensive Groebner basis for them.
  Usage
    (F, GG) = cgbOnGraph(G,d)
  Inputs
    G: List
      A list consisting of a list of vertices and a list of edges.
    d: ZZ
      A postive integer
  Outputs
    F: List
      A list of polynomials
    GG: List
      The Comprehensive Groebner Basis of the polynomials
  Description
    Text
      Let $G=(V,E)$ be graph and fix a positive integer $d$.
      Consider the paramaterised polynomial systems $F=\{f_e\}_{e\in E}\subseteq K[\lambda_e\:e\in E][x_{v,k}:v\in V,1\leq k \leq d]$,
      where $K\in \{\mathbb{C},\mathbb{R}\}$ and
      \[   f_{ij}=\sum_{k=1}^{d}(x_{i,k}-x_{j,k})^2  -\lambda_{ij} \].
      cgbOnGraph returns the polynomial systems $F$ and a Combrehensive Groebner Basis of $F$

    Example
      (F,GG)=cgbOnGraph({{1,2,3},{(1,2),(2,3),(3,1)}},1);
      netList F
      GG_0
    
      --cgbOnGraph({{1,2,3,4},{(1,2),(1,3),(1,4),(2,3),(2,4)}},1)

  Caveat
    This function is not set up to take in Type Graph. User will have to convert to list.
  SeeAlso
    ComprehensiveGBs

///


-* Test section *-
TEST ///
-* Testing ringOrder on various polynomial rings *-
debug needsPackage "ComprehensiveGBs";

RGRevLex = QQ[a..d];
RLex = QQ[a..d, MonomialOrder => Lex];
RGLex = QQ[a..d, MonomialOrder => GLex];
RWeights = QQ[a..d, MonomialOrder => {Weights => {1, 3, 2, 4}, Lex}];
REliminate = QQ[a..d, MonomialOrder => Eliminate 2];
RGroupLex = QQ[a..d, MonomialOrder => GroupLex => 2, Global => false];
RGroupRevLex = QQ[a..d, MonomialOrder => GroupRevLex => 2, Global => false];
RProduct = QQ[a..d, MonomialOrder => ProductOrder {2, 2}];
RBlock = QQ[a..d, MonomialOrder => {Lex => 2, GRevLex => 2}];
RRevLex = QQ[a..d, MonomialOrder => RevLex, Global => false];

assert(ringOrder RGRevLex === {GRevLex => {1, 1, 1, 1}});
assert(ringOrder RLex === {Lex => 4});
assert(ringOrder RGLex === {Weights => {1, 1, 1, 1}, Lex => 4});
assert(ringOrder RWeights === {Weights => {1, 3, 2, 4}, Lex => 4});
assert(ringOrder REliminate === {Weights => {1, 1}, GRevLex => {1, 1, 1, 1}});
assert(ringOrder RGroupLex === {GroupLex => 2, GRevLex => {1, 1}});
assert(ringOrder RGroupRevLex === {GroupRevLex => 2, GRevLex => {1, 1}});
assert(ringOrder RProduct === {GRevLex => {1, 1}, GRevLex => {1, 1}});
assert(ringOrder RBlock === {Lex => 2, GRevLex => {1, 1}});
assert(ringOrder RRevLex === {RevLex => 4});
///


TEST /// 
-* Testing  CGBMain on a*x+b*y *-

Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aR = promote (params#0 , Rtest);
bR = promote (params#1 , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {});

expected1 = ({},aR, {aR*xR + bR*yR});
expected2 = ({aR},bR,{aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({aR,bR}, 1_Rtest, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///


TEST /// 
-* Testing  CGB on a*x+b*y  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest});

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);
///


TEST /// 
-* Testing cgbOnGraph  on  E = {(1,2)}, V = {1,2} *-

E = {(1,2)};
V = {1,2};
G = {V,E};

(F,GG) = cgbOnGraph(G,2);



Rtest = ring first F;


Stest = coefficientRing Rtest;

x11 = Rtest_0;
x12 = Rtest_1;
x21 = Rtest_2;
x22 = Rtest_3;

w12 = promote(Stest_0,Rtest);

expectedF = {x11^2 - 2*x11*x21 + x21^2 + x12^2 - 2*x12*x22 + x22^2 - w12 };
expectedGG = {
    ({}, 1, expectedF)
};

assert(F == expectedF);
assert(GG == expectedGG);

///


TEST /// 
-* Testing  CGBMain on a*x+b*y  with Verbose option *-
Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aR = promote (params#0 , Rtest);
bR = promote (params#1 , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {}, Verbose => true);

expected1 = ({},aR, {aR*xR + bR*yR});
expected2 = ({aR},bR,{aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({aR,bR}, 1_Rtest, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);


///


TEST /// 
-* Testing  CGB on a*x+b*y  with Verbose option  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, Verbose=> true);

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);

///


TEST /// 
-*Testing  CGB on a*x+b*y  with Strategy => "radical" option  *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, Strategy=> "radical");

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected1 or result#1 == expected2);
///



TEST /// 
-* Testing  CGB on a*x+b*y  with Strategy => "radical" option *-

Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aR = promote (params#0 , Rtest);
bR = promote (params#1 , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {}, Strategy => "radical");

expected1 = ({},aR, {aR*xR + bR*yR});
expected2 = ({aR},bR,{aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({aR,bR}, 1_Rtest, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///


TEST /// 
-* Testing  CGBMain on a*x+b*y  with ReduceStrata => true option *-
Ptest = QQ[a,b];
Rtest = Ptest[x,y, MonomialOrder => Lex];

params = gens Ptest;
variables = gens Rtest

aR = promote (params#0 , Rtest);
bR = promote (params#1 , Rtest);
   
xR = variables#0;
yR = variables#1;


resultTest = CGBMain({aR*xR + bR*yR}, {},  ReduceStrata => true);

expected1 = ({},aR, {aR*xR + bR*yR});
expected2 = ({aR},bR,{aR^2*xR + aR*bR*yR, aR*xR + bR*yR});
expected3 = ({aR,bR}, 1_Rtest, {aR*xR + bR*yR});

assert(#resultTest == 3);

assert member(expected1, resultTest);
assert member(expected2, resultTest);
assert member(expected3, resultTest);

///

TEST /// 
-* Testing  CGBMain on a*x+b*y  with ReduceStrata => true option *-
PTest = QQ[aTest,bTest];
RTest = PTest[xTest,yTest, MonomialOrder => Lex];

fTest = aTest*xTest + bTest*yTest;

expected1 = aTest*xTest + bTest*yTest;
expected2 = aTest^2*xTest + aTest*bTest*yTest;

result = CGB({fTest}, ReduceStrata=> true);

assert(#result == 2);
assert(result#0 == expected1 or result#1 == expected1);
assert(result#0 == expected2 or result#1 == expected2);

///

-----------------------------
--TEST for MDBasis
-----------------------------
TEST /// -* Testing MDBasis on {a*x^2 − y, a*y^2 − 1, a*x − 1, (a + 1)*x − y, (a + 1)*y − a} *-
U = U = QQ[a, MonomialOrder => Lex];
R = U[x, y, MonomialOrder => Lex];
G = {a*x^2 - y, a*y^2 - 1, a*x - 1, (a + 1)*x - y, (a + 1)*y - a}
MDBasis(G)
///


------------------------------------------------
--TEST for PGBMain
-- From Example 6.1 of 
-- "An efficient algorithm for computing a 
-- comprehensive Gröbner system of a parametric 
-- polynomial system", D. Kapur Y. Sun D. Wang, 
-- J. of Symbolic Computation issue 49, 2013
------------------------------------------------
TEST /// -* Testing PGBMain on {a*x-, b*y-a, c*x^2-y, c*y^2-x} *-
U := QQ[a, b, c, MonomialOrder => GRevLex]
R := U[x,y,z, MonomialOrder => GRevLex]
G := {a*x-b, b*y-a, c*x^2-y, c*y^2-x}
L := PGBMain(CGBFromTriple({{0_U}, {1_U}, G}))
U' = ring first first first L
R' = ring first last first L
ExpResult = set{
  {
    set ((f -> sub(f, U')) \ {0}),
    set ((f -> sub(f, U')) \ {b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}),
    set ((f -> sub(f, R')) \ {1})
    },
  {
    set ((f -> sub(f, U')) \ {b*c^2-b, a*c^2-a, b^3*c-a^3, a^3*c-b^3, a^6-b^6}),
    set ((f -> sub(f, U')) \ {a*b}),
    set ((f -> sub(f, R')) \ {a^2*y-b^2*c, b*x-a*c*y})
  },
  {
    set ((f -> sub(f, U')) \ {b, a}),
    set ((f -> sub(f, U')) \ {c}),
    set ((f -> sub(f, R')) \ {c*x^2-y, c*y^2-x})
    },
  {
    set ((f -> sub(f, U')) \ {c, b, a}),
    set ((f -> sub(f, U')) \ {1_U'}),
    set ((f -> sub(f, R')) \ {y, x})
    }
}
LSet = set for stratum in L list for i from 0 to 2 list set (stratum_i)

ring first (L_3)_1 -- Problem is that this element is in ZZ and not U'
ring first (L_2)_1 -- ... like this element

assert((new Set from L) == ExpResult )

///


end--



-* Development section *-
restart
debug needsPackage "ComprehensiveGBs"
check "ComprehensiveGBs"

uninstallPackage "ComprehensiveGBs"
restart
installPackage "ComprehensiveGBs"
viewHelp "ComprehensiveGBs"


Description
       Text
       Tree
       Example
       CannedExample
     Acknowledgement
     Contributors
     References
     Caveat
     SeeAlso
     Subnodes

doc ///
     Key
     Headline
     Usage
       degreeMap phi
     Inputs
       phi: ...
     Outputs
     Consequences
       Item
     Description
       Text
       Example
       CannedExample
       Code
       Pre
     ExampleFiles
     Contributors
     References
     Caveat
     SeeAlso

     ///

