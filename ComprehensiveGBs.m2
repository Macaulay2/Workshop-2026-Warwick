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
        { Name => "Sam Knight", Email => "samdeckardknight@gmail.com", HomePage => ""}
        { Name => "Agustina Cagliero", Email => "mariaagustina.cagliero@kuleuven.be", HomePage => ""}
        { Name => "Giulia Gaggero", Email => "gaggerog@mcmaster.ca", HomePage => ""}
        },

    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {} -- functions, objects to export

-* Code section *-

extendedRing = method()
extendedRing (PolynomialRing) := R -> (
  var = gens R;
  coeff = gens baseRing R;
  base = baseRing baseRing R;
  return(base[l, var, coeff]);  -- ordering of variables requires l >> var >> coeff
);

CGBMain = method();
CGBMain (List, List) := (F, S) ->(
  print("1");
  if 1 % (ideal S) == 0 then (
    return {}
  );
  R = ring F_0;
  RExt = extendedRing(R);
  A = apply(F, i -> l *sub(i, RExt));
  B = apply(S, i -> (l-1) *sub(i, RExt));
  gb(ideal join(A, B));
);

-- R = QQ[u, x];
-- F = {x^2-x, x^3-1};
-- S = {u-1};
-- CGBMain(F, S)


-- TODO: implement cgbMain, cgb
-- input system F subset of K[u_1 .. u_m][x_1 .. x_n]  (assumed form of poly ring)






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
