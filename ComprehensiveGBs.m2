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
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""},,
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => ""},,
        { Name => "Giulia Gaggero", Email => "gaggerog@mcmaster.ca", HomePage => ""},
        { Name => "Woody Cohen", Email => "2597103@swansea.ac.uk", HomePage => ""}
        },

    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {} -- functions, objects to export

-* Code section *-

extendedRing = method();
extendedRing (PolynomialRing) := R -> (
  var := gens R;
  coeff := gens baseRing R;
  base := baseRing baseRing R;
  return(base[local l, var, coeff]);  -- ordering of variables requires l >> var >> coeff
);

aux = method();
aux (RingElement) := (h) -> (
  return h
);

CGBMain = method();
CGBMain (List, List) := (F, S) -> (
  print("Computing CGB for F = " | toString F | " and S = " | toString S);
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
  pruneG := select(G, g -> ((leadTerm g) % l == 0) and any(X, i -> member(sub(i, RFlat), support leadCoefficient sub(g, RFlat[l]))));
  pruneG' := apply(pruneG, g -> leadCoefficient sub(g, RExt'));
  h := lcm pruneG';
  -- H := pruneG'; (takes too long to terminate if we do not factor h)
  hfac := factor h;
  H := apply(#hfac, i -> if isConstant hfac#i#0 then 1 else hfac#i#0);
  return {(S, sub(h, R), apply(G, g -> sub(sub(g, {l => 1}), R)))} | flatten apply(H, hi -> CGBMain(F, append(S, sub(hi, R))))
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
CGBMain(F, S)
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







-* Documentation section *-

beginDocumentation()

doc ///
  Key
    ComprehensiveGBs
  Headline
    A package for computing Comprehensive Groebner Bases (CGBs)
///


-* Test section *-
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
