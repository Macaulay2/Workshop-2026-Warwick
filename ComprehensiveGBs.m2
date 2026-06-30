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

export {
    "CGBMain",
    "CGB"
    } -- functions, objects to export

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

listOfFactors = method();
listOfFactors (RingElement) := (h) -> (
  hfac := factor h;
  return apply(#hfac, i -> if isConstant hfac#i#0 then 1 else hfac#i#0)
);

squareFreePart = method();
squareFreePart (RingElement) := (h) -> (
  return product listOfFactors h
);

CGBMain = method();
CGBMain (List, List) := (F, S) -> (
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
  pruneG := select(G, g -> ((leadTerm g) % l == 0) and any(X, i -> member(sub(i, RFlat), support leadCoefficient sub(g, RFlat[l]))));
  pruneG' := apply(pruneG, g -> leadCoefficient sub(g, RExt'));
  h := lcm pruneG';

  if pruneG' == {} then (
      return {(S, sub(h, R), for g in G list (
                  g' := sub(sub(g, {l => 1}), R);
                  if zero g' then continue;
                  g'))}
      );

  -- H := pruneG'; -- (takes too long to terminate if we do not factor h)
  -- H := unique apply(pruneG', g -> squareFreePart g); -- (takes a bit longer to terminate)

  H := listOfFactors h; --See end of section 2 of suzuki sato to for justification. 
                        --THIS IS NOT PROVEN IN THE PAPER, just claimed.
  return {(S, sub(h, R), for g in G list (
                  g' := sub(sub(g, {l => 1}), R);
                  if zero g' then continue;
                  g'))} | flatten apply(H, hi -> CGBMain(F, append(S, sub(hi, R))))
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
  E = apply(t_0, p2 -> sub(p2, R'));
  N = sub(t_1, R');
  G = apply(t_2, p1 -> sub(p1, R') % ideal ({0_(R')} | E));
  I = first entries gens eliminate(ideal G, {x, y});
  print("E = " | toString E | ", N = {" | toString squareFreePart N | "}");
  print("Ideal after eliminating {x, y}: " | toString I);
  print("");
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
    result
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

end

d=2
E={(1,2),(1,3),(2,3),(1,4),(2,4),(3,4)}
V={1,2,3,4}
G={V,E}

cgbOnGraph=method()
cgbOnGraph(List,ZZ):=(G,d)->(
  V:=G_0;
  E:=G_1;
  x:=getSymbol "x";
  w:=getSymbol "w";
  S:=QQ[toSequence apply(E, l -> w_l)];
  R:=S[x_(V_0,1)..x_(V_(#V-1),d)];
  F:=for i in E list(sum(1..d,k->(R_(2*i_0+k-3)-R_(2*i_1+k-3))^2)-S_(position(E, j -> j === i)));
  CGB(F)
)
d=2
E={(1,2),(1,3),(2,3)}
V={1,2,3}
G={V,E}
cgbOnGraph(G,2)


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


----------------------------------
--Cleaning up the output of CGBs
----------------------------------

R = QQ[a, b][x, y, z];
F = {x^3-a, y^4-b, x+y-z};
S = {};
GB = CGBMain(F, S);
noEmptyGB = select(GB, i-> not(member(i_1, i_0)));
XX = new Set from apply(noEmptyGB, i -> i_2);
*-
count = 0;

minimalStrata = for x in elements XX list (
  print(length x);
  strata = select (noEmptyGB, i -> i_2 == x);
  temp = new Set from flatten(apply(strata, i -> i_0));
  for s in strata do (
    temp = temp * (new Set from s_0); 
  );
  count = count + length strata;
  print("S = ", temp, "\t h=", strata_0_1);
  print("count =", count);
  minimal = select(strata, i-> (new Set from i_0)===temp);
  first minimal
);