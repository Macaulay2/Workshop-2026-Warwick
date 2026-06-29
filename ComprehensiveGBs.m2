newPackage(
    "ComprehensiveGBs",
    Version => "0.1",
    Date => "",
    Headline => "A package for computing Comprehensive Groebner Bases (CGBs)",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {} -- functions, objects to export

-* Code section *-


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
