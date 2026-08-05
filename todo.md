# TODOs


    1. ** Ollie ** Add an optional argument `Depth => -1` to CGB functions that such that
    whenever it recurses, the Depth is decremented by 1 and if the Depth reaches 0 then
    we do not recurse (so putting Depth => 0 would return just the generic stratum for example)

    2. ** Angelo, Giulia, Agustina ** Kapur-Sun-Wang (KSW) algorithm (consistency.m2)
    
    3. ** Ollie ** In the SS (CGBMain) - we can create a computation object type (Similar / compatible with
    CGBTriple from consistency.m2) that holds all the objects (Rings, Maps, etc). Currently, this
    is just a list:
    
    ```macaulay2
    RingsandThings := {R,X,RExt,RFlat,RExt',RU,RFlatl};
  
    ```
    
    4. ** Lorenzo ** More optimisations to SS / documentation of them: we can use profiling to check what
    takes a long time and see if it suggests a optimisation.
    
    ```macaulay2
    -- profiling - see what else is taking time

    needsPackage "ComprehensiveGBs"
    R = QQ[a,b][x,y,z, MonomialOrder => Lex]
    F = {x^3 - a, y^4 - b, x+y-z}
    profile CGBMain(F, {});
    profileSummary
    ```
    
    5. ** Weijia ** In SS (CGBMain), construct a monomial order for `RExt` that extends the ordering in R.
    Currently, we just use a Lex order:
    
    ```macaulay2
    R := ring F_0;
    X := gens R;
    U := gens baseRing R;
    K := baseRing baseRing R;
    RExt := K[getSymbol "l", X, U, MonomialOrder => Lex]; -- maybe construct the ordering from R?
    ```
    
    6. ** Agustina ** Code clean-up: I would prefer to use maps instead of 'sub' and a few other small M2 code things
    
    7. Check the completeness of the Docs and Tests
   
    8. ** Lorenzo ** In TestAudit package, what does a 'Silenced Test' mean?
    
    
# Future and long term TODOs

    1. I would like to look into the Bigatti et al. paper: https://link.springer.com/article/10.1007/s00200-025-00684-8 and see if we can implement this algorithm too
    
    2. Speed testing across all the different algorithms
    
# DONE
