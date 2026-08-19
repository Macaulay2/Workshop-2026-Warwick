# TODOs


1. ** Ollie ** [DONE] Add an optional argument `Depth => -1` to CGB functions that such that
whenever it recurses, the Depth is decremented by 1 and if the Depth reaches 0 then
we do not recurse (so putting Depth => 0 would return just the generic stratum for example)

- TODO: return the correct result in CGBMainRec before going through the list H 

2. ** Angelo, Giulia, Agustina ** Kapur-Sun-Wang (KSW) algorithm (consistency.m2)
- [DONE] Moved to main file, now can (almost) delete consistency.m2
- Determine what should happen if listDiff is empty 

2.1 **Everyone** In the KSW algorithm there are some optimisations for the consistency check in Section 5
  this involves three algorithms (1,2,3) that are checked in some order and if all fail then the standard
  consistency check is used.
- [1 of 3 DONE] Add the algorithms
- Write a consistency check method that combines them all
- [FUTURE] think about whether the consistency check method should use hooks
- [FUTURE] understand the optimisations in Section 7 

3. ** Ollie, Angelo ** In the SS (CGBMain) - we can create a computation object type (Similar / compatible with
CGBTriple from consistency.m2) that holds all the objects (Rings, Maps, etc). Currently, this
is just a list:

```macaulay2
RingsandThings := {R,X,RExt,RFlat,RExt',RU,RFlatl};

```
- Add the ring maps to this objects
- Include the ring maps to this object too 
- Move lists of elements in a ring to a single row matrix of elements in the ring : this allows us to apply maps to
  matrices, we will implicitly check that elements belong to the correct ring because the ring of the matrix is fixed 

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

Profiling shows that the nested sub(sub(g, {l => 1}), R) operation in the different returns is executed 690 times and accounts for about 36% of the runtime. 
Can we replace it with a precomputed ring map (RExt \to R) evaluating (l) at 1, and reuse the converted Gröbner basis?

5. ** Weijia ** In SS (CGBMain), construct a monomial order for `RExt` that extends the ordering in R.
Currently, we just use a Lex order:

```macaulay2
R := ring F_0;
X := gens R;
U := gens baseRing R;
K := baseRing baseRing R;
RExt := K[getSymbol "l", X, U, MonomialOrder => Lex]; -- maybe construct the ordering from R?
```
- Think about what happens to Weight orders - maybe they need to be shifted into the right position
  or maybe it's okay - so we should add a test 

6. ** Agustina ** Code clean-up: I would prefer to use maps instead of 'sub' and a few other small M2 code things

7. Check the completeness of the Docs and Tests

8. **Ollie ask Doug/Anton** For mapping elements of a ring to say their coefficient ring, what is the correct way? sub? lift?

9. Investigate the CGBMain algorithm, there seems to be a problem SS CGBMain. Here is an example,
which is also contained in the examples.m2 file:

```macaulay2
U = QQ[a,b,c, MonomialOrder => GRevLex]
R = U[x,y, MonomialOrder => GRevLex]

U = QQ[a,b,c, MonomialOrder => Lex]
R = U[x,y, MonomialOrder => Lex]

F={a*x-b,b*y-a,c*x^2-y,c*y^2-x}
T = CGBFromTriple({{0_U}, {1_U}, F})
L= PGBMain(T)
netList oo

LL = apply(CGBMain(F, {}, ReduceStrata => true), e -> toList e)
netList oo
```
These two methods should return something similar / compatible but they are very different.

Notice that in the generic stratum, there is an element `b*c^2-b` in the SS-CGB but that condition
does not appear in second column. Investigate the line that defines and modifies `pruneG` [line 191-2],
there may be a mistake with the implementation or the write up on the line that defines $\{h_1, \dots, h_\ell\} := \dots$.

# Future and long term TODOs

1. I would like to look into the Bigatti et al. paper: https://link.springer.com/article/10.1007/s00200-025-00684-8 and see if we can implement this algorithm too

2. Speed testing across all the different algorithms

# DONE

8. ** Lorenzo ** In TestAudit package, what does a 'Silenced Test' mean? (fixed, ScoreReport: 100 out of 100)
