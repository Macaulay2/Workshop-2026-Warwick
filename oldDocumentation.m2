-*
doc ///
    Key
        (image,ToricVectorBundle,Matrix)
    Headline
        the image of a vector bundle under a morphism
    Usage
        E1 = image(E,M)
    Inputs
        E:ToricVectorBundle
        M:Matrix
            over @TO ZZ@ or @TO QQ@
    Outputs
        E1:ToricVectorBundle
    Description
        Text
            @TT "M"@ must be a matrix over @TO ZZ@ or @TO QQ@ where the source space is the space of
            the bundle, i.e., the matrix must have $k$ columns if the bundle has rank $k$. Then the
            new bundle is given on each ray $\rho$ by the following filtration of
            image$(E,M)^\rho := M(E^\rho)$ :
        Text
            image$(E,M)^\rho(i) := M(E^\rho(i))$.
        Example
            E = tangentBundle hirzebruchFan 2
            E = E ** E
            M = matrix {{1,0,1,0},{0,1,0,1/1}}
            E1 = image(E,M)
            details E1
    SeeAlso
        (coker,ToricVectorBundle,Matrix)
        (ker,ToricVectorBundle,Matrix)
///

doc ///
    Key
        (ker,ToricVectorBundle,Matrix)
    Headline
        the kernel of a morphism to a vector bundle
    Usage
        E1 = ker(E,M)
    Inputs
        E:ToricVectorBundle
        M:Matrix
            over @TO ZZ@ or @TO QQ@
    Outputs
        E1:ToricVectorBundle
    Description
        Text
            @TT "M"@ must be a matrix over @TO ZZ@ or @TO QQ@ where the source space is the space of
            the bundle, i.e., the matrix must have $k$ columns if the bundle has rank $k$. Then the
            new bundle is given on each ray $\rho$ by the following filtration of
            ker$(E,M)^\rho := $ ker$(M) \cap (E^\rho)$ :
        Text
            ker$(E,M)^\rho(i) := $ ker$(M) \cap E^\rho(i)$.
        Example
            E = tangentBundle hirzebruchFan 2
            E = E ** E
            M = matrix {{1,0,1,0},{0,1,0,1/1}}
            E1 = ker(E,M)
            details E1
    SeeAlso
        (coker,ToricVectorBundle,Matrix)
        (image,ToricVectorBundle,Matrix)
///

doc ///
    Key
        (maxCones,ToricVectorBundle)
    Headline
        the list of maximal cones of the underlying fan
    Usage
        L = maxCones E
    Inputs
        E:ToricVectorBundle
    Outputs
        L:List
            of cones
    Description
        Text
            Returns the list of maximal cones of the underlying fan. These are the cones that
            generate the fan, i.e., are not a face of another. See @TO "Polyhedra::Fan"@,
            @TO "Polyhedra::maxCones"@ and @TO "Polyhedra::Cone"@.
        Example
            E = tangentBundle pp1ProductFan 2
            L = maxCones E
            apply(L,rays)
        Example
            E = tangentBundleKaneyama(pp1ProductFan 2)
            L = maxCones E
            apply(L,rays)
    SeeAlso
        "Polyhedra::Fan"
        "Polyhedra::maxCones"
        "Polyhedra::Cone"
        charts
        (fan,ToricVectorBundle)
        (rays,ToricVectorBundle)
///
*-
-*
doc ///
    Key
        addFiltration
        (addFiltration,ToricVectorBundle,List)
    Headline
        changing the filtration matrices of a toric vector bundle in Klyachko's description
    Usage
        F = addFiltration(E,L)
    Inputs
        E:ToricVectorBundle
        L:List
            with matrices over @TO ZZ@
    Outputs
        F:ToricVectorBundle
    Description
        Text
            @TT "addFiltration"@ replaces the filtration matrices in @TT "E"@ by the matrices in the
            @TO List@ @TT "L"@. The matrices in @TT "L"@ must be $1$ by $k$ matrices over @TO ZZ@,
            where $k$ is the rank of the vector bundle @TT "E"@. The list has to contain one matrix
            for each ray of the underlying fan over which @TT "E"@ is defined. Note that in @TT "E"@
            the rays are already sorted and that the filtration matrices in @TT "L"@ will be
            assigned to the rays in that order. To see the order, use @TO (rays,ToricVectorBundle)@.
        Text
            The filtration on the vector bundle over a ray is given by the filtration matrix for
            this ray in the following way: The first index $j$, such that the $i$-th basis vector in
            the basis over this ray appears in the $j$-th step of the filtration, is the $i$-th
            entry of the filtration matrix. OR in other words, the $j$-th step step in the
            filtration is given by all columns of the basis matrix for which the corresponding entry
            in the filtration matrix is less or equal to $j$.
        Text
            The matrices need not satisfy the compatibility condition. This can be checked with
            @TO isWellDefined@.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2)
            details E
            F = addFiltration(E,{matrix{{1,3}},matrix{{-1,3}},matrix{{2,-3}},matrix{{0,-1}}})
            details F
            isWellDefined F
        Text
            This means that for example over the first ray the first basis vector of the filtration
            of @TT "F"@ appears at the filtration step 1 and the second at 3.
    SeeAlso
        filtration
        addBase
        isWellDefined
///

doc ///
    Key
        base
        (base,ToricVectorBundleKaneyama)
    Headline
        the basis matrices for the rays
    Usage
        b = base E
    Inputs
        E:ToricVectorBundle
    Outputs
        b:HashTable
    Description
        Text
            The basis of a toric vector bundle in Klyachko's description is given for each ray as a
            square matrix of rank $k$ of the bundle. The output is a @TO HashTable@ where the keys
            are the rays of the fan given as one column matrices over @TO ZZ@, and for each ray a
            $k$ by $k$ matrix over @TO QQ@ and $k$ is the rank of the bundle.
        Example
            E = tangentBundle hirzebruchFan 3
            base E
    SeeAlso
        addBase
        filtration
        isWellDefined
///


doc ///
    Key
        charts
        (charts,ToricVectorBundleKaneyama)
    Headline
        the number of maximal affine charts
    Usage
        n = charts E
    Inputs
        E:ToricVectorBundle
    Outputs
        n:ZZ
    Description
        Text
            The function @TT "charts"@ returns the number of maximal cones in the underlying fan,
            i.e., the number of affine charts.
        Example
            E = cotangentBundle pp1ProductFan 3
            charts E
    SeeAlso
        "Polyhedra::Fan"
        (fan,ToricVectorBundle)
///


doc ///
    Key
        (coker,ToricVectorBundle,Matrix)
    Headline
        the cokernel of a morphism to a vector bundle
    Usage
        E1 = coker(E,M)
    Inputs
        E:ToricVectorBundle
        M:Matrix
            over @TO ZZ@ or @TO QQ@
    Outputs
        E1:ToricVectorBundle
    Description
        Text
            @TT "M"@ must be a matrix over @TO ZZ@ or @TO QQ@ where the target space is the space of
            the bundle, i.e., the matrix must have $k$ rows if the bundle has rank $k$. Then the new
            bundle is given on each ray $\rho$ by the following filtration of
            coker(E,M)${}^\rho = ( E^{\rho} ) / $im(M) :
        Text
            --coker(E,M)${}^\rho(i) := E^{\rho}(i) / ( E^{\rho}(i) \cap $ im(M) ).
        Example
            E = tangentBundle hirzebruchFan 2
            E = E ** E
            M = matrix {{1,0},{0,1},{1,0},{0,1/1}}
            --E1 = coker(E,M)
            --details E1
    SeeAlso
        (image,ToricVectorBundleMap)
        (ker,ToricVectorBundleMap)
///


doc ///
    Key
        existsDecomposition
        (existsDecomposition,ToricVectorBundle,List)
    Headline
        checks if a list of matrices of weight vectors for each maximal cone admits a decomposition
    Usage
        b = existsDecomposition(E,L)
    Inputs
        E:ToricVectorBundle
        L:List
    Outputs
        b:Boolean
            whether there exists a decomposition
    Description
        Text
            The list @TT "L"@ must have one entry for each maximal cone $\sigma$ in the underlying
            fan $\Sigma$ of @TT "E"@. If the rank of the bundle is $k$ and the ambient dimension of
            the variety is $n$ then each entry must either be an $n$ by $k$ matrix over @TO ZZ@ or a
            list of these. Then it checks for each maximal cone in the fan (given in the order of
            @TO (maxCones,ToricVectorBundle)@) if for any of the matrices in the corresponding entry
            in @TT "L"@ these weight vectors admit a decomposition of the bundle into torus
            eigenspaces. See @HREF("http://math.stanford.edu/~sampayne/", "Sam Payne's")@
            @EM "Moduli of toric vector bundles"@, Compositio Math. 144, 2008. Lemma 3.5.
        Text
            One can for example use the output of the function @TO findWeights@.
        Example
            E = tangentBundle projectiveSpaceFan 3
            L = findWeights E
            existsDecomposition(E,L)
        Text
            Note that the data given in the description of @TT "E"@ defines an equivariant vector
            bundle on the toric variety exactly if there exists a set of weight vectors for each
            maximal cone that admits a decomposition. The function @TO isWellDefined@ uses this.
    Caveat
        @TT "existsDecomposition"@ is known to produce incorrect output.
    SeeAlso
        findWeights
        isWellDefined
///

doc ///
    Key
        filtration
        (filtration,ToricVectorBundle)
    Headline
        the filtration matrices of the vector bundle
    Usage
        f = filtration E
    Inputs
        E:ToricVectorBundle
    Outputs
        f:HashTable
    Description
        Text
            For each ray of the fan there is a filtration matrix. If the bundle has rank $k$ then
            this is a one row matrix over @TO ZZ@ with $k$ entries. This defines the filtration on
            the corresponding base matrix (see @TO base@) such that the $j$-th filtration is
            generated by all columns of the base matrix for which the entry in the same column of
            the filtration matrix is less or equal to $j$.
        Example
            E = tangentBundle hirzebruchFan 2
            filtration E
        Text
            So in this example for each ray the first column of the basis appears at -1 and the
            second at 0.
    SeeAlso
        addFiltration
        base
        isWellDefined
///

doc ///
    Key
        findWeights
        (findWeights,ToricVectorBundle)
    Headline
        finds the possible weight vectors for the maximal cones
    Usage
        L = findWeights E
    Inputs
        E:ToricVectorBundle
    Outputs
        L:List
    Description
        Text
            The list @TT "L"@ contains a list for each maximal cone $\sigma$ of the underlying fan.
            For each maximal cone $\sigma$ this list contains all matrices of possible weight
            vectors, that induce the filtrations on the rays of this cone (modulo permutations, but
            yet not all permutations). This means that for one of these matrices $M$ multiplied with
            the matrix $R$ of rays of this cone (the rays are the rows) gives the matrix of
            filtrations of these rays (where for each filtration the entries may be permuted).
        Example
            E = tangentBundle projectiveSpaceFan 3
            findWeights E
    SeeAlso
        filtration
        existsDecomposition
        isWellDefined
///
*-
doc ///
    Key
        (ring,ToricVectorBundle)
    Headline
        the graded ring of the bundle
    Usage
        R = ring E
    Inputs
        E:ToricVectorBundle
    Outputs
        R:Ring
    Description
        Text
            For a vector bundle in Kaneyama's description the graded ring is @TO QQ@ with degree
            space the lattice of the underlying fan.
        Example
            E = tangentBundleKaneyama(projectiveSpaceFan 3)
            ring E
        Text
            For a vector bundle in Klyachko's description the graded ring is @TO QQ@ with degree
            space the lattice of the underlying fan.
        Example
            E = toricVectorBundle(1,projectiveSpaceFan 2, toList(3:matrix{{1/2}}),toList(3:matrix{{-1}}))
            ring E
    SeeAlso
        (cohomology,ZZ,ToricVectorBundle)
        (cohomology,ZZ,ToricVectorBundle,Matrix)
        (cohomology,ZZ,ToricVectorBundle,List)
///
doc ///
    Key
        (rank,ToricVectorBundle)
    Headline
        the rank of the vector bundle
    Usage
        r = rank E
    Inputs
        E:ToricVectorBundle
    Outputs
        r:ZZ
    Description
        Text
            Returns the rank $r$ of the toric vector bundle in Kaneyama's description.
        Example
            E = tangentBundle projectiveSpaceFan 3
            rank E
    SeeAlso
        (rays,ToricVectorBundle)
        (fan,ToricVectorBundle)
        charts
///

doc ///
    Key
        (dual,ToricVectorBundle)
    Headline
        the dual bundle of a toric vector bundle
    Usage
        Ed = dual E
    Inputs
        E:ToricVectorBundle
    Outputs
        Ed:ToricVectorBundle
    Description
        Text
            @TT "dual"@ computes the dual vector bundle of a toric vector bundle.
        Example
            E = tangentBundleKaneyama(pp1ProductFan 2)
            Ed = dual E
            details Ed
            Ed == cotangentBundleKaneyama(pp1ProductFan 2)
        Example
            E = tangentBundle projectiveSpaceFan 2
            Ed = dual E
            details Ed
            Ed == cotangentBundle projectiveSpaceFan 2
    SeeAlso
        tangentBundle
        cotangentBundle
///
