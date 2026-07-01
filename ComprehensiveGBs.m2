newPackage(
    "ComprehensiveGBs",
    Version => "0.1",
    Date => "",
    Headline => "A package for computing Comprehensive Groebner Bases (CGBs)",
    Authors => {{ Name => "", Email => "", HomePage => ""},
        { Name => "Lorenzo De Biase", Email => "lorenzo.debiase@enea.it", HomePage => "https://sites.google.com/viewlorenzodebiase/"},
        { Name => "Weijia Wang", Email => "weijia.wang@lip6.fr", HomePage => "https://weijia.perso.lip6.fr/"},
        { Name => "Angelo El Saliby", Email => "angelo.el.saliby@mis.mpg.de", HomePage => "angeloelsaliby.github.io"},
        { Name => "Oliver Clarke", Email => "oliver.clarke@durham.ac.uk", HomePage => "https://www.oliverclarkemath.com"},
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""},
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => ""},
        { Name => "Giulia Gaggero", Email => "gaggerog@mcmaster.ca", HomePage => ""},
        { Name => "Woody Cohen", Email => "2597103@swansea.ac.uk", HomePage => ""}
        },
    Keywords => {""},
    AuxiliaryFiles => false,
    PackageImports => {"MinimalPrimes"},
    DebuggingMode => true
    )

export {
    "CGBMain",
    "CGB",
    "cgbOnGraph"
    } -- functions, objects to export

protect CGBMainTriples

-* Code section *-

listOfFactors = method()
listOfFactors (RingElement) := (h) -> (
  hfac := factor h;
  apply(#hfac, i -> if isConstant hfac#i#0 then 1_(ring h) else hfac#i#0)
);

squareFreePart = method()
squareFreePart (RingElement) := (h) -> (
  product listOfFactors h
);

isConsistent = method();
isConsistent (List, List) := (E, N) -> (
  I := radical ideal E;
  any(N, p -> not isMember(p, I))
);

diffLC = method();
diffLC (Sequence, Sequence) := (A, B) -> (
  result := {(A#0 | {B#1}, A#1)} | apply(B#0, p -> (A#0, A#1 * p));
  select(result, t -> isConsistent(t#0, {t#1}))
);

diffConstructibleByLC = method();
diffConstructibleByLC (List, Sequence) := (C, LC) -> (
  flatten apply(C, t -> diffLC(t, LC))
);

CGBMain = method();
CGBMain (List, List) := (F, S) -> (
  CGBMainRec(F, S, {})
)

CGBMainRec = method();
CGBMainRec (List, List, List) := (F, S, memo) -> (
  --print("Computing CGB for F = " | toString F | " and S = " | toString S);
  if 1 % (ideal S) == 0 then (
    return {}
  );
  R := ring F_0;
  X := gens R;
  U := gens baseRing R;
  K := baseRing baseRing R;
  RExt := K[getSymbol "l", X, U, MonomialOrder => Lex]; -- maybe construct the ordering from R?
  l := first gens RExt;
  RFlat := K[X, U, MonomialOrder => Lex];
  RExt' := K[U][l, X, MonomialOrder => Lex];
  A := apply(F, i -> l * sub(i, RExt));
  B := apply(S, i -> (l-1) * sub(i, RExt));
  G := (entries gens gb(ideal join(A, B)))_0;
  pruneG := select(G, g -> ((first first exponents(leadMonomial sub(g,RExt))) > 0) and any(exponents(sub(leadCoefficient sub(g,RFlat[getSymbol "l"]),RFlat)), i -> any(i_(toList(0..(#X-1))), i -> i > 0)));
  pruneG = apply(pruneG, g -> leadCoefficient sub(g, RExt'));
  h := lcm pruneG;

  memo = memo | {(S, sub(h, R), for g in G list (
                  g' := sub(sub(g, {l => 1}), R);
                  if zero g' then continue;
                  g'))};

  if pruneG == {} then (
    return memo
  );

  -- H := pruneG; -- (takes too long to terminate if we do not factor h)
  -- H := unique apply(pruneG, g -> squareFreePart g); -- (takes a bit longer to terminate)

  H := listOfFactors h;
  RU := K[U];
  diffset := {};
  for hi in H do (
    diffset = {({sub(hi, RU)}, 1_RU)};
    for t in memo do (
      diffset = diffConstructibleByLC(diffset, (apply(t#0, p -> sub(p, RU)), sub(t#1, RU)));
      if isEmpty diffset then (
        break
      );
    );
    if isEmpty diffset then (
      continue;
    );
    memo = CGBMainRec(F, append(S, sub(hi, R)), memo);
  );
  return memo
);

-*
R = QQ[u][x];
F = {x^2-x, x^3-1};
S = {u-1};
CGBMain(F, S)
*-

-*
R = QQ[a, b][x, y, z];
F = {x^3-a, y^4-b, x+y-z};
S = {};
L = CGBMain(F, S);
print("");

R' = QQ[x, y, z, a, b, MonomialOrder => Lex];
for t in L do (
  E = apply(t_0, p -> sub(p, R'));
  N = sub(t_1, R');
  G = apply(t_2, p -> sub(p, R'));
  I = first entries gens eliminate(saturate(ideal (E | G), ideal N), {x, y});
  print("E = " | toString E | ", N = {" | toString squareFreePart N | "}");
  print("Minimal polynomial of z: " | toString last I);
);
*-

-- Order of confidence:
-- 

-- TODO: implement cgb



CGB=method()
CGB(List):=F->(
    s:=first entries eliminateVariables(F);
    result:=s;
    G:=CGBMain(F,s);
    for i in G do (
        result=result|(i_2);
        );
    unique result
)


eliminateVariables=method()
eliminateVariables(List):=F->(
    R:=ring first F;
    n:=numgens(R);
    m:=numgens(coefficientRing(R));
    x:=getSymbol "x";
    u:=getSymbol "u";
    S:=QQ[x_1..x_n,u_1..u_m, MonomialOrder => Eliminate n];
    U:=gens coefficientRing(R);
    X:=gens R;
    l1:=for i from 0 to m-1 list U_i=>S_(i+n);
    l2:=for j from 0 to n-1 list X_j=>S_j;
    F':=apply(F,h->sub(h,l1|l2));
    F'gbgens:=gens gb(ideal(F'));
    S':=selectInSubring(1,F'gbgens);
    C:=coefficientRing R;
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






-* Documentation section *-

beginDocumentation()

doc ///
  Key
    ComprehensiveGBs
  Headline
    A package for computing Comprehensive Groebner Bases (CGBs). Based on @HREF("#ref1","[1]")@.
  References
    @LABEL("[1]","id" => "ref1")@ Akira Suzuki and Yosuke Sato. 2006. A simple algorithm to compute comprehensive Gröbner bases using Gröbner bases. In Proceedings of the 2006 international symposium on Symbolic and algebraic computation (ISSAC '06). Association for Computing Machinery, New York, NY, USA, 326–331. https://doi.org/10.1145/1145768.1145821
///


-* Test section *-
TEST /// -* Testing  CGBMain on a*x+b*y *-

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


TEST /// -* Testing  CGB on a*x+b*y  *-
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


TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed

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
     Inputs
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



Example:
R=QQ[a,b,c][x,y]
f=a*x^2+4*b*y^4
g=a*b*x*y^3-5*x^2*y
F={f,g,f+a^2}
debug ComprehensiveGBs
eliminateVariables(F)

n=numgens(R)
m=numgens(coefficientRing(R))
S=QQ[x_1,x_2,u_1,u_2,u_3, MonomialOrder => Eliminate n]
gens S
sub(f,{a=>u_1,b=>u_2,c=>u_3,x=>x_1,y=>x_2})

U=gens coefficientRing(R)
X=gens R
l1=for i from 0 to m-1 list U_i=>S_(i+n)
l2=for j from 0 to n-1 list X_j=>S_j

F'=apply(F,h->sub(h,l1|l2))
gb(ideal(F'))
F'gbgens=gens gb(ideal(F'))

l1=for i from 0 to m-1 list S_(i+n)=>U_i
H= first o27
S'=selectInSubring(1,F'gbgens)
first entries S'
C=coefficientRing R
m=map(C,ring S',
    toList(n:0)|gens C   
    )
m(S')

R=QQ[a,b,c][x,y,z]
f=x^3-a
g=y^4-b
h=x+y-z
F={f,g,h}
debug ComprehensiveGBs
eliminateVariables(F)
CGB(F)
