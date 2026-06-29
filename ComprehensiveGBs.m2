newPackage(
    "ComprehensiveGBs",
    Version => "0.1",
    Date => "",
    Headline => "A package for computing Comprehensive Groebner Bases (CGBs)",

    Authors => {{ Name => "", Email => "", HomePage => ""},
        { Name => "Lorenzo De Biase", Email => "lorenzo.debiase@enea.it", HomePage => "https://sites.google.com/viewlorenzodebiase/"},
        { Name => "Weijia Wang", Email => "weijia.wang@lip6.fr", HomePage => "https://weijia.perso.lip6.fr/"},
        { Name => "Angelo El Saliby", Email => "angelo.el.saliby@mis.mpg.de", HomePage => "angeloelsaliby.github.io"},
        { Name => "Oliver Clarke", Email => "oliver.clarke@durham.ac.uk", HomePage => ""},
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""},
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => ""},
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
CGBMain (List, List) := (F, S) ->(
  print("1");
  if 1 % (ideal S) == 0 then (
    return {}
  );
  R := ring F_0;
  RExt := extendedRing(R);
  l := first gens RExt;
  A := apply(F, i -> l * sub(i, RExt));
  B := apply(S, i -> (l-1) * sub(i, RExt));
  G := (entries gens gb(ideal join(A, B)))_0;
  pruneG := select(G, g -> (leadTerm(g) % l == 0) and any(gens R, i -> leadTerm(g) % i == 0)) -- test if this line works 30th
);

-- R = QQ[u, x];
-- F = {x^2-x, x^3-1};
-- S = {u-1};
-- CGBMain(F, S)

-- Order of confidence:
-- 

-- TODO: implement cgbMain, cgb
-- input system F subset of K[u_1 .. u_m][x_1 .. x_n]  (assumed form of poly ring)



CGB=method()
CGB(List):=F->(





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
F={f,g}

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
selectInSubring(1,F'gbgens)
