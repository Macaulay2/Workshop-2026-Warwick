
---------------------------------------
-- DOCUMENTATION
---------------------------------------

beginDocumentation()

doc ///
    Key
        ToricVectorBundles
    Headline
        computations involving equivariant vector bundles on normal toric varieties
    Description
        Text
            This package implements the construction of equivariant vector bundles on toric varieties
            as well as the computation of several of their properties, such as cohomology, Euler
            characteristic, first Chern class, among others.
        Text
            A toric vector bundle on a toric variety $X$ is a vector bundle $\mathcal{E}$ on $X$ which
            admits an action of the dense torus $T_X \subset X$ that is equivariant with respect
            to the projection map $\pi \colon \mathcal{E} \rightarrow X$ and $T_X$ acts linearly on
            the fibres of $\mathcal{E}$.
        Text
            There are several ways to describe a toric vector bundle. The primary method that this package
            employs is via Klyachko's description: a toric vector bundle corresponds to a collection of
            filtrations of the fibre over the torus identity (which is a vector space $E$), one for each
            ray of the base toric variety, satisfying a compatibility condition. This is the main type @TO ToricVectorBundle@.
        Example
            X = hirzebruchSurface 2;
            TX = tangentBundle X;
            displayFiltrations TX
        Text
            The package also provides various translations into other presentations. For instance, Altmann,
            Hochenegger, and Witt showed that toric vector bundles correspond to stratifications of $E$ by torus-fixed divisors;
            see @HREF("https://arxiv.org/abs/2412.03476", "Toric sheaves and polyhedra")@ for more details.
        Example
            W = weilDecoration TX;
            netList strata W
        Text
            Another translation provided is to modules over the Cox ring. Since toric vector bundles are
            coherent sheaves, they may be represented by a finitely generated multigraded module. We provide
            a presentation of such a module.
        Example
            M = klyachkoToModule TX
            displayFiltrations moduleToKlyachko(X, M)
    References
        For mathematical background see @UL { {"Tamafumi Kaneyama,",EM "On equivariant
        vector bundles on an almost homogeneous variety", ", Nagoya Math. J. 57, 1975."},
        {"Alexander A. Klyachko,",EM "Equivariant bundles over toral varieties", ", Izv. Akad.
        Nauk SSSR Ser. Mat., 53, 1989."}, {"Markus Perling,",EM "Resolution and moduli for
        equivariant sheaves over toric varieties", ", PhD Thesis, 2003."} }@
    Contributors
        This package was originally developed by René Birkner, @HREF("https://www.sfu.ca/~nilten/", "Nathan Ilten")@
        and Lars Petersen. The following people have generously contributed code or improved existing code:
        @HREF("https://mahrud.github.io/", "Mahrud Sayrafi")@, and
        @HREF("https://mast.queensu.ca/~ggsmith/", "Gregory G. Smith")@.
    Caveat
        The implementation of vector bundles in Kaneyama's description only supports pure and full
        dimensional fans. Furthermore, it relies on computations in the @TO Polyhedra@ package.
    SeeAlso
        "NormalToricVarieties"
///

doc ///
    Key
        ToricVectorBundle
    Headline
        the class of all toric vector bundles in Klyachko's description
    Description
        Text
            Klyachko gave a complete characterization of toric vector bundles, which is summarized by
            the following theorem:
        Text
            @TT "The category of toric vector bundles on the toric variety "@$X$@TT " is equivalent 
            to the category of finite dimensional "@$k$@TT"-vector spaces "@$E$@TT" with collections 
            of decreasing filtrations "@$\{E^{\rho}(i)| i \in{} \mathbb{Z}\}$@TT", indexed by rays in 
            "@$\rho \in \Sigma_X(1)$@TT", satisfying the following compatibility condition: For each 
            maximal "@$\sigma \in \Sigma_X$@TT" there is a decomposition "@$E = \oplus_{u \in{} M_\sigma} E_u$@TT" 
            such that "@$E^{\rho}(i) = \sum_{(u,v_\rho) \leq i} E_u$@TT" for every ray "@$\rho \in{} \sigma$@TT" 
            and every "@$i \in{} \mathbb{Z}$.
        Text
            In this implementation, the data of the filtrations is stored using a matrix which describes
            a basis for $E$, together with a list of indices indicating the largest positions where the $i$th
            column of the matrix appears in the filtration of $E$. For instance, consider the tangent bundle
            on $\mathbb{P}^2$.
        Example
            X = toricProjectiveSpace 2;
            TX = tangentBundle X;
            displayFiltrations TX
        Text
            Focusing on the filtration corresponding to the ray  {-1, -1}, the basis chosen is
            $\begin{bsmallmatrix} -1 & -1 \\ -1 & 0 \end{bsmallmatrix}$. The first column,
            $\begin{bsmallmatrix} -1 \\ -1 \end{bsmallmatrix}$, lies in the column space of all of the matrices
            until index 1. The second column $\begin{bsmallmatrix} -1 \\ 0 \end{bsmallmatrix}$ appears in
            the column space of all of the matrices until index 0. Hence we record these largest positions.
        Example
            F = filtrations TX
            (filtrationJumps TX)_0 == {1,0}
        Text
            An individual filtered piece may be recovered using @TO filteredPiece(ToricVectorBundle,List,ZZ)@.
        Example
            filteredPiece(TX,{-1,-1},1)
        Text
            The user need not input filtrations which satisfy the compatibility conditions. To verify that the
            compatibility conditions are satisfied, one runs @TO isLocallyFree@. For instance, we can break
            the compatibilty of the tangent bundle by simply changing one of the filtered pieces.
        Example
            TX' = toricVectorBundle(X, filtrationMatrices TX, {{0,0},{1,0},{1,0}});
            displayFiltrations TX'
            isLocallyFree TX'
    SeeAlso
        toricVectorBundle
        displayFiltrations
        filtrations
        details
        filteredPiece
        weilDecoration
        klyachkoToModule
        moduleToKlyachko
        ToricVectorBundleKaneyama
///

-*
doc ///
    Key
        ToricVectorBundleKaneyama
    Headline
        the class of all toric vector bundles in Kaneyama's description
    Description
        Text
            Consider an equivariant vector bundle $E$ of rank $k$ on a toric variety $X$
            corresponding to a fan $\Sigma$. Then $E$ is trivial on any invariant open affine
            subvariety of $X$ and moreover homogeneously generated by $k$ elements. Furthermore, the
            transition maps between these trivializations are homogeneous of degree zero. Thus,
            after fixing local homogeneous generators, we get a list of degrees of generators for
            each cone in $\Sigma$, along with a transition map for each pair of cones. Conversely,
            given a list of $k$ degrees for every cone of $\Sigma$ along with transition maps
            satisfying compatibility and regularity conditions for every pair of cones, one can
            construct an equivariant vector bundle of rank $k$ on $X$.
        Text
            This description of equivariant vector bundles, due to Kaneyama, is implemented for
            complete, pointed fans in the following way: It is only necessary to consider charts
            corresponding to maximal dimensional cones of $\Sigma$. Furthermore, each
            codimension-one cone of $\Sigma$ corresponds to a pair of maximal dimensional cones, and
            thus to a transition map. Due to the compatibility condition for transition maps, one
            can reconstruct the transition map corresponding to an arbitrary pair from the maps of
            this sort. If the dimension of $\Sigma$ is $n$ then for each maximal dimensional cone
            the degree list of the corresponding chart is saved as an $n$ times $k$ matrix over 
            $\mathbb{Z}$, giving $k$ degree vectors in the dual lattice of the fan, one for each local
            generator of the bundle. Additionally, for every pair of maximal cones intersecting in a
            common codimension-one face, there is a matrix in GL($k$,$\mathbb{Q}$), representing the
            transition map between these two affine charts. Indeed, suppose that cones $\sigma_1$
            and $\sigma_1$ intersect in some codimension-one face, with corresponding affine charts
            $U_1$ and $U_2$. Then on the intersection, the $i$-th generator for $U_1$ has a unique
            representation as a linear combination in the generators for $U_2$ after being
            multiplied with characters to all have the required degree. The coefficients in this
            representation form the $i$-th column of the desired matrix.
        Text
            We briefly consider the example of $\mathbb{P}^2$, corresponding to the complete fan
            with rays through $(0,1)$, $(1,0)$, and $(-1,-1)$. Denote by $x$ the character of weight
            $[1,0]$ and by $y$ the character of weight $[0,1]$. Now the coordinate rings of the
            three standard affine charts of $\mathbb{P}^2$ are generated by respectively
            $(x^{ -1},x^{ -1}y)$, $(x,y)$, and $(xy^{ -1},y^{ -1})$. This means that the modules of
            differentials are generated by respectively $(d(x^{ -1}),d(x^{ -1}y))$, $(dx,dy)$, and
            $(d(xy^{ -1}),d(y^{ -1}))$. These modules give us local trivializations of the cotangent
            bundle on $\mathbb{P}^2$. The degrees of the generators for the first chart then are
            $[-1,0]$ and $[-1,1]$, for example. Now, since $d(x^{ -1})=-x^{ -2}dx$ and
            $d(x^{ -1}y) = -x^{ -2}ydx + x^{ -1}dy$, we get that the transition map between the
            generators of the first and second chart is given by the matrix with columns $(-1,0)$
            and $(-1,1)$.
        Text
            An instance of class ToricVectorBundle, when displayed or printed, gives an
            overview of the characteristics of the bundle:
        Example
            E = cotangentBundle(projectiveSpaceFan 2,"Type" => "Kaneyama")
        Text
            To see all relevant details of a bundle use @TO details@. The data described above is
            all stored in a single hash table. In the example from above, the first chart has the
            key 0, and transition map described above has key (0,1):
        Example
            details E
    Caveat
        This implementation only supports vector bundles where the corresponding transition maps
        have coefficients in @TO QQ@.
    SeeAlso
        ToricVectorBundle
        ToricVectorBundle
///

doc ///
    Key
        addBaseChange
        (addBaseChange,ToricVectorBundleKaneyama,List)
    Headline
        changing the transition matrices of a toric vector bundle
    Usage
        F = addBaseChange(E,L)
    Inputs
        E:ToricVectorBundleKaneyama
        L:List
            with matrices over @TO ZZ@ or @TO QQ@
    Outputs
        F:ToricVectorBundleKaneyama
    Description
        Text
            @TT "addBaseChange"@ replaces the transition matrices in @TT "E"@ by the matrices in the
            @TO List@ @TT "L"@. The matrices in @TT "L"@ must be in GL($k$,@TO ZZ@) or
            GL($k$,@TO QQ@), where $k$ is the rank of the vector bundle @TT "T"@. The list has to
            contain one matrix for each maximal dimensional cone of the underlying fan over which
            @TT "E"@ is defined. The fan can be recovered with @TO (fan,ToricVectorBundle)@. The
            vector bundle already has a list of pairs $(i,j)$ denoting the codim 1 intersections of
            two maximal cones with $i<j$ and they are ordered in lexicographic order. The matrices
            will be assigned to the pairs $(i,j)$ in that order. To see which codimension 1 cone
            corresponds to the pair $(i,j)$ use @TO (details,ToricVectorBundle)@. The matrix $A$
            assigned to $(i,j)$ denotes the transition $(e_i^1,...,e_i^k) = (e_j^1,...,e_j^k)*A$.
            The matrices need not satisfy the regularity or the cocycle condition. These can be
            checked with @TO regCheck@ and @TO cocycleCheck@.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2,"Type" => "Kaneyama")
            details E
            F = addBaseChange(E,{matrix{{1,2},{0,1}},matrix{{1,0},{3,1}},matrix{{1,-2},{0,1}},matrix{{1,0},{-3,1}}})
            details F
            cocycleCheck F
    SeeAlso
        addDegrees
        regCheck
        cocycleCheck
///

doc ///
    Key
        addBase
        (addBase,ToricVectorBundle,List)
    Headline
        changing the basis matrices of a toric vector bundle in Klyachko's description
    Usage
        F = addBase(E,L)
    Inputs
        E:ToricVectorBundle
        L:List
            with matrices over @TO ZZ@ or @TO QQ@
    Outputs
        F:ToricVectorBundle
    Description
        Text
            @TT "addBase"@ replaces the basis matrices in @TT "E"@ by the matrices in the @TO List@
            @TT "L"@. The matrices in @TT "L"@ must be in GL($k,R$), where $k$ is the rank of the
            vector bundle @TT "E"@ and $R$ is @TO ZZ@ or @TO QQ@. The list has to contain one matrix
            for each ray of the underlying fan over which @TT "E"@ is defined. Note that in @TT "E"@
            the rays are already sorted and that the basis matrices in @TT "L"@ will be assigned to
            the rays in that order. To see the order use @TO (rays,ToricVectorBundle)@.
        Text
            The matrices need not satisfy the compatibility condition. This can be checked with
            @TO isWellDefined@.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2)
            details E
            F = addBase(E,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
            details F
            isWellDefined F
    SeeAlso
        base
        addFiltration
        isWellDefined
///

doc ///
    Key
        addDegrees
        (addDegrees,ToricVectorBundleKaneyama,List)
    Headline
        changing the degrees of a toric vector bundle
    Usage
        F = addDegrees(E,L)
    Inputs
        E:ToricVectorBundleKaneyama
        L:List
            with matrices over @TO ZZ@
    Outputs
        F:ToricVectorBundleKaneyama
    Description
        Text
            @TT "addDegrees"@ replaces the degree matrices in @TT "E"@ by the matrices in the
            @TO List@ @TT "L"@. The matrices in @TT "L"@ must be $n$ by $k$ matrices over @TO ZZ@,
            where $k$ is the rank of the vector bundle @TT "E"@ and $n$ is the dimension of the
            underlying toric variety. The list has to contain one matrix for each maximal
            dimensional cone of the underlying fan over which @TT "E"@ is defined. Note that in
            @TT "E"@ the top dimensional cones are already sorted and that the degree matrices in
            @TT "L"@ will be assigned to the cones in that order. To find out the order use
            @TO (maxCones,ToricVectorBundle)@. The matrices need not satisfy the regularity
            condition. This can be checked with @TO regCheck@.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2,"Type" => "Kaneyama")
            details E
            F = addDegrees(E,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
            details F
            regCheck F
    SeeAlso
        addBaseChange
        regCheck
        cocycleCheck
///

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
        areIsomorphic
        (areIsomorphic,ToricVectorBundle,ToricVectorBundle)
    Headline
        checks if two vector bundles are isomorphic
    Usage
        b = areIsomorphic(E,F)
    Inputs
        E:ToricVectorBundle
        F:ToricVectorBundle
    Outputs
        b:Boolean
            whether @TT "E"@ and @TT "F"@ are isomorphic
    Description
        Text
            @TT "E"@ and @TT "F"@ must be vector bundles over the same fan and the filtrations must
            be defined over the same ring. Two equivariant vector bundles in Klyachko's description
            are isomorphic if there exists a simultaneous isomorphism for the filtered vector spaces
            of all rays. The method then returns whether the bundles are isomorphic.
        Example
            HF = hirzebruchFan 2
            E = exteriorPower(2, cotangentBundle HF)
            F = weilToCartier({-1,-1,-1,-1},HF)
            areIsomorphic(E,F)
        Text
            To obtain the isomorphism, if two bundles are isomorphic use
            @TO (isomorphism,ToricVectorBundle,ToricVectorBundle)@.
    Caveat
        If @TT "E"@ and @TT "F"@ are defined over different rings (e.g. @TT "QQ"@ and @TT "ZZ"@)
        then @TT "areIsomorphic(E,F)"@ will return @TT "false"@. Likewise, if the bundles are only
        defined over @TT "ZZ"@, the function will check for an isomorphism of the filtrations over
        @TT "ZZ"@.
    SeeAlso
        (isomorphism,ToricVectorBundle,ToricVectorBundle)
        base
        filtration
        details
///

doc ///
    Key
        base
        (base,ToricVectorBundle)
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
        cartierIndex
        (cartierIndex,List,Fan)
    Headline
        the Cartier index of a Weil divisor
    Usage
        N = cartierIndex(L,F)
    Inputs
        L:List
        F:Fan
            a pure and full dimensional fan
    Outputs
        N:ZZ
    Description
        Text
            @TT "L"@ must be a list of weights, exactly one for each ray of the fan. Then the
            Cartier index is the smallest strictly positive natural number $N$ such that $N$ times
            the Weil divisor is Cartier. If the Weil divisor defined by these weights is not
            @TO QQ@-Cartier, then $N$ would be infinity. In this case @TT "cartierIndex"@ returns an
            error. Otherwise it returns $N$.
        Example
            F = fan posHull matrix {{1,5},{5,1}}
            L = {2,2}
            cartierIndex(L,F)
        Text
            If we change the Weil divisor we get a different Cartier index:
        Example
            L = {3,3}
            cartierIndex(L,F)
    Caveat
        The ordering of the list @TT "L"@ must correspond to the ordering of the rays of the fan
        output by @TO raySortOfFan@.
    SeeAlso
        weilToCartier
///

doc ///
    Key
        charts
        (charts,ToricVectorBundle)
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
        cocycleCheck
        (cocycleCheck,ToricVectorBundleKaneyama)
    Headline
        checks if a toric vector bundle fulfills the cocycle condition
    Usage
        b = cocycleCheck E
    Inputs
        E:ToricVectorBundleKaneyama
    Outputs
        b:Boolean
            whether @TT "E"@ satisfies the cocyle condition
    Description
        Text
            The transition matrices in @TT "E"@ define an equivariant toric vector bundle if they
            satisfy the cocycle condition. I.e. in this implementation of complete fans this means
            that for every codimension 2 cone of the fan the cycle of transition matrices of
            codimension 1 cones containing the codimension 2 cone gives the identity when
            multiplied.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2,"Type" => "Kaneyama")
            details E
            A = matrix{{1,2},{0,1}};
            B = matrix{{1,0},{3,1}};
            C = matrix{{1,-2},{0,1}};
            E1 = addBaseChange(E,{A,B,C,matrix{{1,0},{0,1}}})
            cocycleCheck E1
            D = inverse(B)*A*C
            E1 = addBaseChange(E,{A,B,C,D})
            cocycleCheck E1
    SeeAlso
        addBaseChange
        addDegrees
        regCheck
///

doc ///
    Key
        (cohomology,ZZ,ToricVectorBundle)
    Headline
        the i-th cohomology group of a toric vector bundle
    Usage
        c = HH^i E
    Inputs
        i:ZZ
        T:ToricVectorBundle
    Outputs
        c:Module
    Description
        Text
            Computes the $i$-th cohomology group of the toric vector bundle $E$. The output is the
            $i$-th cohomology group as a multigraded module. For this, it computes the set of all
            degrees that can give non-zero cohomology (see @TO deltaE@). This set is finite if the
            underlying toric variety is complete. If the toric variety is not complete then an error
            is returned.
        Text
            The computation of the cohomology groups for a toric vector bundle given in terms of
            Kaneyama is done by the usual Cech cohomology complex, again separately for every degree
            $u \in{} M$.
        Text
            If the option @TT "Degree => 1"@ is used then it displays the number of degrees for
            which it computes the cohomology. $i$ must be between $0$ and the dimension of the
            underlying toric variety.
        Example
            E = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama")
            HH^0 E
            HH^0 (E,Degree => 1)
        Text
            In case the toric vector bundle $E$ is given in Klyachko's description, there is a
            special exact sequence of finite dimensional vector spaces for every weight $u \in{} M$
            whose cohomology groups in degree $i$ are isomorphic to $H^i(X,E)$. This exact sequence
            can be found in the Klyachko's paper listed on the main page of the documentation.
        Text
            If the option @TT "Degree => 1"@ is used then it displays the number of degrees for
            which it computes the cohomology. $i$ must be between $0$ and the dimension of the
            underlying toric variety.
        Example
            E = tangentBundle hirzebruchFan 3
            HH^0 E
            HH^0 (E,Degree => 1)
    SeeAlso
        (ring,ToricVectorBundle)
        deltaE
        (cohomology,ZZ,ToricVectorBundle,Matrix)
        (cohomology,ZZ,ToricVectorBundle,List)
        (hh,ZZ,ToricVectorBundle)
        eulerChi
///

doc ///
    Key
        (cohomology,ZZ,ToricVectorBundle,List)
    Headline
        the i-th cohomology of a toric vector bundle for a given list of degrees
    Usage
        c = HH_i^E L
    Inputs
        i:ZZ
        E:ToricVectorBundle
        L:List
            containing weights of the form, one column matrix over @TO ZZ@
    Outputs
        c:List
    Description
        Text
            Computes the $i$-th cohomology of the toric vector bundle $E$ for a given list of
            degrees. For this $i$ must be between $0$ and the rank of the vector bundle. The entries
            of the list @TT "L"@ must be one column matrices each defining a point in the lattice of
            the fan over which $E$ is defined
        Example
            E = tangentBundle hirzebruchFan 3
            HH_0^E {matrix{{1},{0}},matrix{{-1},{0}}}
    SeeAlso
        (ring,ToricVectorBundle)
        deltaE
        (cohomology,ZZ,ToricVectorBundle)
        (cohomology,ZZ,ToricVectorBundle,Matrix)
        (hh,ZZ,ToricVectorBundle)
        eulerChi
///

doc ///
    Key
        (cohomology,ZZ,ToricVectorBundle,Matrix)
    Headline
        the i-th cohomology of a toric vector bundle in a given degree
    Usage
        c = HH_i^E u
    Inputs
        i:ZZ
        E:ToricVectorBundle
        u:Matrix
            over @TO ZZ@ with just one column, giving a weight in the lattice
    Outputs
        c:Module
    Description
        Text
            Computes the $i$-th cohomology group of the toric vector bundle $E$ of degree $u$ where
            $u$ must be a one-column matrix giving a point in the lattice of the fan over which $E$
            is defined and $i$ must be between $0$ and the dimension of the underlying toric
            variety.
        Example
            E = tangentBundle hirzebruchFan 3
            HH^0 (E,matrix{{1},{0}})
    SeeAlso
        (ring,ToricVectorBundle)
        deltaE
        (cohomology,ZZ,ToricVectorBundle)
        (cohomology,ZZ,ToricVectorBundle,List)
        (hh,ZZ,ToricVectorBundle)
        eulerChi
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
            coker(E,M)${}^\rho(i) := E^{\rho}(i) / ( E^{\rho}(i) \cap $ im(M) ).
        Example
            E = tangentBundle hirzebruchFan 2
            E = E ** E
            M = matrix {{1,0},{0,1},{1,0},{0,1/1}}
            E1 = coker(E,M)
            details E1
    SeeAlso
        (image,ToricVectorBundle,Matrix)
        (ker,ToricVectorBundle,Matrix)
///

doc ///
    Key
        cotangentBundle
        (cotangentBundle,Fan)
    Headline
        the cotangent bundle on a toric variety
    Usage
        E = cotangentBundle F
    Inputs
        F:Fan
    Outputs
        E:{ToricVectorBundleKaneyama, ToricVectorBundle}
    Description
        Text
            If the fan @TT "F"@ is pure, of full dimension and smooth, then the function generates
            the cotangent bundle of the toric variety given by @TT "F"@. If no further options are
            given then the resulting bundle will be in Klyachko's description:
        Example
            F = projectiveSpaceFan 2
            E = tangentBundle F
            details E
        Text
            If the option @TT "\"Type\" => \"Kaneyama\""@ is given then the resulting bundle will be
            in Kaneyama's description:
        Example
            F = projectiveSpaceFan 2
            E = tangentBundle(F,"Type" => "Kaneyama")
            details E
    SeeAlso
        tangentBundle
///

doc ///
    Key
        deltaE
        (deltaE,ToricVectorBundle)
    Headline
        the polytope of possible degrees that give non zero cohomology
    Usage
        P = deltaE E
    Inputs
        E:ToricVectorBundle
    Outputs
        P:Polyhedron
    Description
        Text
            For a toric vector bundle over a complete toric variety there is a finite set of degrees
            $u$ such that the degree $u$ part of the cohomology of the vector bundle is non-zero.
            This function computes a polytope $\Delta_E$, such that these degrees are contained in
            this polytope. If the underlying toric variety is not complete then an error is
            returned.
        Example
            X = toricProjectiveSpace 1 ** toricProjectiveSpace 1
            E = trivialBundle(X,2)
            P = deltaE E
            vertices P
            E1 = tangentBundle X
            P1 = deltaE E1
            vertices P1
    SeeAlso
        eulerChi
        (cohomology,ZZ,ToricVectorBundle)
        (hh,ZZ,ToricVectorBundle)
///

doc ///
    Key
        details
        (details,ToricVectorBundle)
    Headline
        the details of a toric vector bundle
    Usage
        ht = details E
    Inputs
        E:ToricVectorBundle
    Outputs
        ht:Sequence
            or @TO HashTable@ if the bundle is in Klyachko's description
    Description
        Text
            For a toric vector bundle in Kaneyama's description, the sequence @TT "ht"@ contains a
            hash table that assigns to each maximal cone $\sigma$ of the underlying fan its matrix
            of rays and its matrix of degrees, and a hash table giving a transition matrix for every
            pair of maximal cones that intersect in a codimension 1 face.
        Example
            E = tangentBundle(pp1ProductFan 2,"Type" => "Kaneyama")
            details E
        Text
            For a toric vector bundle in Klyachko's description, the hash table @TT "ht"@ contains
            the rays of the underlying fan and for each ray the basis of the bundle over this ray
            and the filtration matrix.
        Example
            E = tangentBundle pp1ProductFan 2
            details E
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
            E = tangentBundle(pp1ProductFan 2,"Type" => "Kaneyama")
            Ed = dual E
            details Ed
            Ed == cotangentBundle(pp1ProductFan 2,"Type" => "Kaneyama")
        Example
            E = tangentBundle projectiveSpaceFan 2
            Ed = dual E
            details Ed
            Ed == cotangentBundle projectiveSpaceFan 2
    SeeAlso
        tangentBundle
        cotangentBundle
///

doc ///
    Key
        eulerChi
        (eulerChi,ToricVectorBundle)
        (eulerChi,Matrix,ToricVectorBundle)
    Headline
        the Euler characteristic of a toric vector bundle
    Usage
        i = eulerChi E
        eulerChi(u,E)
    Inputs
        E:ToricVectorBundle
        u:Matrix
            with just one column over @TO ZZ@ representing a degree vector
    Outputs
        i:ZZ
    Description
        Text
            This function computes the Euler characteristic of a vector bundle if only the bundle is
            given to the function. For this it first computes the set of all degrees that give
            non-zero cohomology (see @TO deltaE@) and then computes the Euler characteristic for
            each these degrees. If the underlying variety is not complete then this set may not be
            finite. Thus, for a non-complete toric variety an error is returned.
        Text
            If in addition a one-column matrix over @TO ZZ@, representing a degree vector @TT "u"@,
            is given, it computes the Euler characteristic of the degree @TT "u"@-part of the vector
            bundle @TT "E"@. For this the variety need not be complete.
        Example
            E = tangentBundle hirzebruchFan 3
            u = matrix {{0},{0}}
            eulerChi(u,E)
            eulerChi E
        Example
            E = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama")
            u = matrix {{0},{0}}
            eulerChi(u,E)
            eulerChi E
    SeeAlso
        deltaE
        (cohomology,ZZ,ToricVectorBundle)
        (hh,ZZ,ToricVectorBundle)
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
        (maxCones,ToricVectorBundle)
///

doc ///
    Key
        (exteriorPower,ZZ,ToricVectorBundle)
    Headline
        the 'l'-th exterior power of a toric vector bundle
    Usage
        Ee = exteriorPower(l,E)
    Inputs
        l:ZZ
            strictly positive
        E:ToricVectorBundle
    Outputs
        Ee:ToricVectorBundle
    Description
        Text
            @TT "exteriorPower"@ computes the @TT "l"@-th exterior power of a toric vector bundle in
            each description. The resulting bundle will be given in the same description as the
            original bundle. @TT "l"@ must be strictly positive and at most equal the rank of the
            bundle.
        Example
            E = tangentBundle hirzebruchFan 3
            details E
            Ee = exteriorPower(2,E)
            details Ee
    SeeAlso
        (symbol ++,ToricVectorBundle,ToricVectorBundle)
        (tensor,ToricVectorBundle,ToricVectorBundle)
        (symmetricPower,ZZ,ToricVectorBundle)
///

doc ///
    Key
        (fan,ToricVectorBundle)
    Headline
        the underlying fan of a toric vector bundle
    Usage
        F = fan E
    Inputs
        E:ToricVectorBundle
    Outputs
        F:Fan
    Description
        Text
            Returns the fan of the underlying toric variety. This is an object of the package
            Polyhedra. See also @TO "Polyhedra::Fan"@.
        Example
            E = tangentBundle hirzebruchFan 3
            F = fan E
            rays F
    SeeAlso
        "Polyhedra::Fan"
        charts
        (maxCones,ToricVectorBundle)
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
            E = tangentBundle(projectiveSpaceFan 3,"Type" => "Kaneyama")
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
        (hh,ZZ,ToricVectorBundle)
    Headline
        the rank of the i-th cohomology group of a toric vector bundle
    Usage
        d = hh^i E
        d = hh^i (E,u)
    Inputs
        i:ZZ
        E:ToricVectorBundle
            and an optional @TT "u"@, @ofClass Matrix@ over @TO ZZ@, giving a point in the lattice
            of the fan
    Outputs
        d:ZZ
    Description
        Text
            @TT "hh^i"@ computes the rank of the $i$-th cohomology group. If no further argument is
            given then it returns the rank of the complete cohomology group. For this it computes
            the set of all degrees that can give non-zero cohomology (see @TO deltaE@). This set is
            finite if the underlying toric variety is complete. If the toric variety is not
            complete, then an error is returned.
        Text
            If in addition a one column matrix $u$ over @TO ZZ@ is given it returns the rank of the
            degree $u$ part of the cohomology group. For this the variety need not be complete.
        Example
            E = tangentBundle hirzebruchFan 2
            u = matrix{{0},{0}}
            hh^0 (E,u)
            hh^0 E
    SeeAlso
        (cohomology,ZZ,ToricVectorBundle)
        (cohomology,ZZ,ToricVectorBundle,Matrix)
        (cohomology,ZZ,ToricVectorBundle,List)
        deltaE
///

doc ///
    Key
        hirzebruchFan
        (hirzebruchFan,ZZ)
    Headline
        the fan of the n-th Hirzebruch surface
    Usage
        F = hirzebruchFan n
    Inputs
        n:ZZ
            positive
    Outputs
        F:Fan
    Description
        Text
            Generates the fan of the $n$-th Hirzebruch surface.
        Example
            F = hirzebruchFan 3
            rays F
    SeeAlso
        "Polyhedra::Fan"
        "Polyhedra::hirzebruch"
        pp1ProductFan
        projectiveSpaceFan
///

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
        isGeneral
        (isGeneral,ToricVectorBundle)
    Headline
        checks whether a toric vector bundle is general
    Usage
        b = isGeneral E
    Inputs
        E:ToricVectorBundle
    Outputs
        b:Boolean
            whether @TT "E"@ is general
    Description
        Text
            A toric vector bundle in Klyachko's description is general if for every maximal cone
            $\Sigma$ in the fan the following condition holds: Let $\rho_1,...,\rho_l$ be the rays
            of $\sigma$. Then for every choice of filtration steps $i_1,...,i_l$ for each ray, i.e.,
            choose an integer for each ray where the filtration enlarges, the equation
        Text
            codim $(\cap E^{\rho_j} ( i_j )) = min \{ \sum ($codim $E^{\rho_j} ( i_j )),rank E \}$
        Text
            holds.
        Example
            E = cotangentBundle hirzebruchFan 2
            isGeneral E
    SeeAlso
        filtration
        base
        randomDeformation
///

doc ///
    Key
        (isomorphism,ToricVectorBundle,ToricVectorBundle)
    Headline
        the isomorphism if the two bundles are isomorphic
    Usage
        M = isomorphism(E,F)
    Inputs
        E:ToricVectorBundle
        F:ToricVectorBundle
    Outputs
        M:Matrix
            over the ring over which the two bundles are defined
    Description
        Text
            Two equivariant vector bundles in Klyachko's description are isomorphic if there exists
            a simultaneous isomorphism for the filtered vector spaces of all rays. If the two
            bundles are isomorphic (see @TO areIsomorphic@) this function returns the isomorphism.
            For this, the two bundles must be defined over the same fan.
        Example
            HF = hirzebruchFan 2
            E = exteriorPower(2, cotangentBundle HF)
            F = weilToCartier({-1,-1,-1,-1},HF)
            M = isomorphism(E,F)
    SeeAlso
        areIsomorphic
        base
        filtration
        details
///

doc ///
    Key
        isWellDefined
        (isWellDefined,ToricVectorBundle)
    Headline
        checks if the data does in fact define an equivariant toric vector bundle
    Usage
        b = isWellDefined E
    Inputs
        E:ToricVectorBundle
    Outputs
        b:Boolean
            whether @TT "E"@ defines a toric vector bundle
    Description
        Text
            If @TT "E"@ is in Klyachko's description then the data in @TT "E"@ defines an
            equivariant toric vector on the toric variety if and only if for each maximal cone
            exists a decomposition into torus eigenspaces of the bundle. See
            @HREF("http://math.stanford.edu/~sampayne/", "Sam Payne's")@
            @EM "Moduli of toric vector bundles"@, Compositio Math. 144, 2008. Section 2.3. This
            uses the two functions @TO findWeights@ and @TO existsDecomposition@.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2)
            E = addBase(E,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
            isWellDefined E
            F = toricVectorBundle(1,normalFan crossPolytope 3)
            F = addFiltration(F,apply({2,1,1,2,2,1,1,2}, i -> matrix {{i}}))
            isWellDefined F
        Text
            If @TT "E"@ is in Kaneyama's description then data in @TT "E"@ defines an equivariant
            toric vector bundle on the toric variety if and only if it satisfies the regularity and
            the cocycle condition (See @TO cocycleCheck@ and @TO regCheck@).
        Example
            E = toricVectorBundle(2,pp1ProductFan 2,"Type" => "Kaneyama")
            isWellDefined E
            E = addBaseChange(E,{matrix{{1,2},{3,1}},matrix{{-1,0},{3,1}},matrix{{1,2},{-3,-1}},matrix{{-1,0},{-3,-1}}})
            isWellDefined E
    Caveat
        @TT "isWellDefined"@ is known to produce incorrect output for Klyachko bundles. The user is
        recommended to instead use @TT "isLocallyFree"@ from the package
        @TT "PositivityToricBundles"@.
    SeeAlso
        findWeights
        existsDecomposition
        addBase
        addFiltration
        cocycleCheck
        regCheck
        addBaseChange
        addDegrees
        details
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
            E = tangentBundle(pp1ProductFan 2,"Type" => "Kaneyama")
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

doc ///
    Key
        (net,ToricVectorBundleKaneyama)
    Headline
        displays characteristics of a toric vector bundle
    Usage
        net E
    Inputs
        E:ToricVectorBundleKaneyama
    Description
        Text
            Displays an overview of the properties of a toric vector bundle, the dimension of the
            variety, the number of affine charts, and the rank of the vector bundle.
        Example
            E = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama");
            net E
    SeeAlso
        (net,ToricVectorBundle)
        details
///

doc ///
    Key
        (net,ToricVectorBundle)
    Headline
        displays characteristics of a toric vector bundle in Klyachko's description
    Usage
        net E
    Inputs
        E:ToricVectorBundle
    Description
        Text
            Displays an overview of the properties of a toric vector bundle, the dimension of the
            variety, the number of affine charts, the number of rays of the fan, and the rank of the
            vector bundle.
        Example
            E = tangentBundle hirzebruchFan 3;
            net E
    SeeAlso
        (net,ToricVectorBundleKaneyama)
        details
///

doc ///
    Key
        pp1ProductFan
        (pp1ProductFan,ZZ)
    Headline
        the fan of n products of PP^1
    Usage
        F = pp1ProductFan n
    Inputs
        n:ZZ
            strictly positive
    Outputs
        F:Fan
    Description
        Text
            Generates the fan of the product of $n$ projective one-spaces. This is the same as the
            normal fan of the $n$ dimensional hypercube.
        Example
            F = pp1ProductFan 2
            rays F
            maxCones F
    SeeAlso
        "Polyhedra::Fan"
        hirzebruchFan
        projectiveSpaceFan
///

doc ///
    Key
        projectiveSpaceFan
        (projectiveSpaceFan,ZZ)
    Headline
        the fan of projective n space
    Usage
        F = projectiveSpaceFan n
    Inputs
        n:ZZ
            strictly positive
    Outputs
        F:Fan
    Description
        Text
            Generates the fan of projective $n$-space.
        Example
            F = projectiveSpaceFan 2
            rays F
            maxCones F
    SeeAlso
        "Polyhedra::Fan"
        hirzebruchFan
        pp1ProductFan
///

doc ///
    Key
        randomDeformation
        (randomDeformation,ToricVectorBundle,ZZ)
        (randomDeformation,ToricVectorBundle,ZZ,ZZ)
    Headline
        a random deformation of a given toric vector bundle
    Usage
        E1 = randomDeformation(E,h)
        E1 = randomDeformation(E,l,h)
    Inputs
        E:ToricVectorBundle
        l:ZZ
            less than @TT "h"@
        h:ZZ
    Outputs
        E1:ToricVectorBundle
    Description
        Text
            For a bundle of rank $k$ the function @TT "randomDeformation"@ replaces each base matrix
            by a random $k$ by $k$ matrix with entries between $l$ and $h$. For this $h$ must be
            greater than $l$. If $l$ is not given then the random entries are between $0$ and $h$
            and then $h$ must be strictly positive.
        Example
            E = tangentBundle pp1ProductFan 2
            details E
            E1 = randomDeformation(E,-2,6)
            details E1
    Caveat
        In general, @TT "randomDeformation"@ will only produce a reflexive sheaf, not a locally free
        one. However, for smooth toric surfaces, equivariant reflexive sheaves are automatically
        locally free.
    SeeAlso
        base
        filtration
        details
        isGeneral
///

doc ///
    Key
        (rank,ToricVectorBundle)
    Headline
        the rank of the vector bundle
    Usage
        k = rank E
    Inputs
        E:ToricVectorBundle
    Outputs
        k:ZZ
    Description
        Text
            Returns the rank $k$ of the toric vector bundle in Kaneyama's description.
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
        (rays,ToricVectorBundle)
    Headline
        the rays of the underlying fan
    Usage
        L = rays E
    Inputs
        E:ToricVectorBundle
    Outputs
        L:List
    Description
        Text
            Returns the rays of the fan of the underlying toric variety as a list. Each ray is given
            as a one column matrix.
        Example
            E = cotangentBundle projectiveSpaceFan 2
            rays E
    SeeAlso
        (rank,ToricVectorBundle)
        (fan,ToricVectorBundle)
        charts
///

doc ///
    Key
        raySortOfFan
    Headline
        The sorted rays of the fan
    Usage
        L = raySortOfFan F
    Inputs
        F:Fan
    Outputs
        L:List
    Description
        Text
            Returns the rays of the fan as a list. Each ray is given as a one column matrix. This
            list is sorted in the same order as is used with all routines involving Klyachko-style
            vector bundles.
        Example
            F = projectiveSpaceFan 2
            raySortOfFan F
///

doc ///
    Key
        regCheck
        (regCheck,ToricVectorBundleKaneyama)
    Headline
        checking the regularity condition for a toric vector bundle
    Usage
        b = regCheck E
    Inputs
        E:ToricVectorBundleKaneyama
    Outputs
        b:Boolean
            whether @TT "E"@ satisfies the regularity condition
    Description
        Text
            For a toric vector bundle in Kaneyama's description, the regularity condition means that
            for every pair of maximal cones $\sigma_1,\sigma_2$intersecting in a common
            codimension-one face, the two sets of degrees $d_1,d_2$ and the transition matrix
            $A_{1,2}$ fulfil the regularity condition. I.e. for every $i$ and $j$ we have that
            either the $(i,j)$ entry of the matrix $A_{1,2}$ is $0$ or the difference of the $i$-th
            degree vector of $d_1$ of $\sigma_1$ and the $j$-th degree vector of $d_2$ of $\sigma_2$
            is in the dual cone of the intersection of $\sigma_1$ and $\sigma_2$.
        Text
            Note that this is only necessary for toric vector bundles generated 'by hand' using
            @TO addBaseChange@ and @TO addDegrees@, since bundles generated for example by
            @TO tangentBundle@ satisfy the condition automatically.
        Example
            E = tangentBundle(pp1ProductFan 2,"Type" => "Kaneyama")
            regCheck E
    SeeAlso
        addBaseChange
        addDegrees
        cocycleCheck
        isWellDefined
///

doc ///
    Key
        (symbol **,ToricVectorBundle,ToricVectorBundle)
    Headline
        the tensor product of two toric vector bundles
    Usage
        E = E1 ** E2
    Inputs
        E1:ToricVectorBundle
        E2:ToricVectorBundle
    Outputs
        E:ToricVectorBundle
    Description
        Text
            If $E_1$ and $E_2$ are defined over the same fan and in the same description, then
            @TT "tensor"@ computes the tensor product of the two vector bundles in this description
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3)
            E2 = tangentBundle hirzebruchFan 3
            E = E1 ** E2
            details E
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3,"Type" => "Kaneyama")
            E2 = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama")
            E = E1 ** E2
            details E
    SeeAlso
        (tensor,ToricVectorBundle,ToricVectorBundle)
        (symbol ++,ToricVectorBundle,ToricVectorBundle)
        (exteriorPower,ZZ,ToricVectorBundle)
        (symmetricPower,ZZ,ToricVectorBundle)
///

doc ///
    Key
        (symbol ++,ToricVectorBundle,ToricVectorBundle)
    Headline
        the direct sum of two toric vector bundles
    Usage
        E = E1 ++ E2
    Inputs
        E1:ToricVectorBundle
        E2:ToricVectorBundle
    Outputs
        E:ToricVectorBundle
    Description
        Text
            If $E_1$ and $E_2$ are defined over the same fan, then @TT "directSum"@ computes the
            direct sum of the two vector bundles. The bundles must both be given in the same
            description and the resulting bundle will be in this description.
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3)
            E2 = tangentBundle hirzebruchFan 3
            E = E1 ++ E2
            details E
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3,"Type" => "Kaneyama")
            E2 = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama")
            E = E1 ++ E2
            details E
    SeeAlso
        (symbol **,ToricVectorBundle,ToricVectorBundle)
        (tensor,ToricVectorBundle,ToricVectorBundle)
        (exteriorPower,ZZ,ToricVectorBundle)
        (symmetricPower,ZZ,ToricVectorBundle)
///

doc ///
    Key
        (symbol ==,ToricVectorBundle,ToricVectorBundle)
    Headline
        checks for equality
    Usage
        b = E1 == E2
    Inputs
        E1:ToricVectorBundle
        E2:ToricVectorBundle
    Outputs
        E:Boolean
            whether the two toric vector bundles are equal
    Description
        Text
            Checks if two toric vector bundles are identical. This only works if they are given in
            the same description.
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3)
            E2 = tangentBundle hirzebruchFan 3
            E1 == E2
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3,"Type" => "Kaneyama")
            E2 = tangentBundle(hirzebruchFan 3,"Type" => "Kaneyama")
            E1 == E2
    SeeAlso
        areIsomorphic
        (isomorphism,ToricVectorBundle,ToricVectorBundle)
///

doc ///
    Key
        (symmetricPower,ZZ,ToricVectorBundle)
    Headline
        the 'l'-th symmetric power of a toric vector bundle
    Usage
        Es = symmetricPower(l,E)
    Inputs
        l:ZZ
            strictly positive
        E:ToricVectorBundle
    Outputs
        Es:ToricVectorBundle
    Description
        Text
            @TT "symmetricPower"@ computes the $l$-th symmetric power of a toric vector bundle in
            each description. The resulting bundle will be given in the same description as the
            original bundle. $l$ must be strictly positive.
        Example
            E = tangentBundle hirzebruchFan 3
            details E
            Es = symmetricPower(2,E)
            details Es
    SeeAlso
        (exteriorPower,ZZ,ToricVectorBundle)
        (symbol ++,ToricVectorBundle,ToricVectorBundle)
        (tensor,ToricVectorBundle,ToricVectorBundle)
///

doc ///
    Key
        tangentBundle
        (tangentBundle,Fan)
    Headline
        the tangent bundle on a toric variety
    Usage
        E = tangentBundle F
    Inputs
        F:Fan
    Outputs
        E:ToricVectorBundle
    Description
        Text
            If the fan @TT "F"@ is pure, of full dimension and smooth, then the function generates
            the tangent bundle of the toric variety given by @TT "F"@. If no further options are
            given then the resulting bundle will be in Klyachko's description:
        Example
            F = pp1ProductFan 2
            E = tangentBundle F
            details E
        Text
            If the option @TT "\"Type\" => \"Kaneyama\""@ is given then the resulting bundle will be
            in Kaneyama's description:
        Example
            F = pp1ProductFan 2
            E = tangentBundle(F,"Type" => "Kaneyama")
            details E
    SeeAlso
        cotangentBundle
///

doc ///
    Key
        (tensor,ToricVectorBundle,ToricVectorBundle)
    Headline
        the tensor product of two toric vector bundles
    Usage
        E = tensor(E1,E2)
    Inputs
        E1:ToricVectorBundle
        E2:ToricVectorBundle
    Outputs
        E:ToricVectorBundle
    Description
        Text
            If @TT "E1"@ and @TT "E2"@ are defined over the same fan and are in the same
            description, then @TT "tensor"@ computes the tensor product of the two vector bundles in
            this description.
        Example
            E1 = toricVectorBundle(2,hirzebruchFan 3)
            E2 = tangentBundle hirzebruchFan 3
            E = tensor(E1,E2)
            details E
    SeeAlso
        (symbol **,ToricVectorBundle,ToricVectorBundle)
        (symbol ++,ToricVectorBundle,ToricVectorBundle)
        (exteriorPower,ZZ,ToricVectorBundle)
        (symmetricPower,ZZ,ToricVectorBundle)
///

doc ///
    Key
        toricVectorBundle
        (toricVectorBundle,ZZ,Fan)
    Headline
        the trivial bundle of rank 'k' for a given fan
    Usage
        E = toricVectorBundle(k,F)
    Inputs
        k:ZZ
            strictly positive
        F:Fan
            an object of class Fan
    Outputs
        E:ToricVectorBundle
    Description
        Text
            For a given pure, full dimensional and pointed Fan @TT "F"@ the function
            @TT "toricVectorBundle"@ generates the trivial toric vector bundle of rank @TT "k"@.
        Text
            If no further options are given then the resulting bundle will be in Klyachko's
            description: The basis assigned to every ray is the standard basis of $\mathbb{Q}^k$ and
            the filtration is given by $0$ for all $i<0$ and $\mathbb{Q}^k$ for $i>=0$.
        Example
            E = toricVectorBundle(2,projectiveSpaceFan 2)
            details E
        Text
            If the option @TT "\"Type\" => \"Kaneyama\""@ is given then the resulting bundle will be
            in Kaneyama's description: The degree vectors of this bundle are all zero vectors and
            the transition matrices are all the identity. Note that for Kaneyama's description only
            complete, pointed fans are implemented and thus a non complete fan will produce an
            error.
        Example
            E = toricVectorBundle(2,pp1ProductFan 2,"Type" => "Kaneyama")
            details E
    SeeAlso
        addBaseChange
        addDegrees
        addBase
        addFiltration
        details
        regCheck
        cocycleCheck
        isWellDefined
///

doc ///
    Key
        toricVectorBundle
        (toricVectorBundle,NormalToricVariety,List,List)
        (toricVectorBundle,NormalToricVariety,HashTable)
    Headline
        a toric vector bundle of rank 'k' with given filtrations or degrees
    Usage
        E = toricVectorBundle(X,L1,L2)
        E = toricVectorBundle(X,H)
    Inputs
        X:NormalToricVariety
        L1:List
          list of matrices (@TO filtrationMatrices@)
        L2:List
          list of integers (@TO filtrationJumps@)
        H:HashTable
          with keys the rays of X and values {Matrix, List}
    Outputs
        E:ToricVectorBundle
    Description
        Text
            Given a @TO "NormalToricVarieties::NormalToricVariety" @TT "X"@ over a field @TT "F"@ and a list of $r\times r$ matrices @TT "L1"@
            having one matrix with entries in @TT "F"@ for each ray in the fan of @TT "X"@
            and a list @TT "L2"@ having a list of $r$ integers for each ray in the fan of @TT "X"@;
            it outputs a @TO toricVectorBundle@ @TT "E"@. This toric vector bundle has as Klyachko description by decreasing filtrations
            being the ones where for a ray $\rho$ in the fan of @TT "X"@ the decreasing filtration defined at the $i$-th
            step by the matrix given by the columns for which the corresponding jump is greater or equal to $i$ (see @TO filteredPiece@). 
            It is assumed that the lists @TT "L1"@ and @TT "L2"@ are ordered according to the way @TO "NormalToricVarieties:: rays"@ of @TT "X"@ is and 
            that the list of jumps is ordered so that the the $j$-th entry of the jumps list is the maximun index for which the $j$-th column appears in the filtration. 

            Alternatively, the input can be given as a pair of a @TO "NormalToricVarieties::NormalToricVariety" @TT "X"@  over a field @TT "F"@ and a HashTable H.
            The HashTable H must have as keys the rays of the fan and for each ray store a list consisting first of a $r\times r$ matrix with entries in @TT "F"@ 
            and a list of $r$ integers.

        Text
            Note that the matrices and the filtration jumps that are given to the function need not
            satisfy the compatibility condition for them to define a toric vector bundle, checked by @TO "PositivityToricBundles::isLocallyFree"@. 
            However, the output is guaranteed to be a reflexive sheaf.
        Example
            X = toricProjectiveSpace 2;
            rays X
            L1 = {matrix {{1_QQ,0},{0,1}},matrix{{0,1_QQ},{1,0}},matrix{{-1_QQ,0},{-1,1}}}
            L2 = {{-1,0},{-2,-1},{0,1}}
            E = toricVectorBundle(X,L1,L2)
            details E
            displayFiltrations E
    Caveat
      Note that entries rays fan X in general orders the rays in a different way that rays X. 
    SeeAlso
        toricVectorBundleKaneyama
        filtrationJumps
        filtrationMatrices
        filteredPiece
        details
        displayFiltrations
///

doc ///
    Key
        twist
        (twist,ToricVectorBundle,List)
        (twist,ToricVectorBundle, ToricDivisor)
    Headline
        twists a toric vector bundle with a line bundle
    Usage
        E1 = twist(E,L)
        E1 = twist(E,D)
    Inputs
        E:ToricVectorBundle
        L:List
        D:ToricDivisor
    Outputs
        E1:ToricVectorBundle
    Description
        Text
            @TT "twist"@ takes a toric vector bundle $E$ in Klyachko's description and a list of
            integers @TT "L"@ or a @TO "NormalToricVaraieties::ToricDivisor"@ @TT "D"@. The list must contain one entry for each ray of the underlying fan.
            Then it computes the twist of the vector bundle by the line bundle given by these
            integers, that is, it computes the @TO tensorProduct@ of the @TO lineBundle@ associated to the list @TT "L"@ (or the toric divisor @TT "D"@).
        Example
            X = hirzebruchSurface 2
            E = tangentBundle X 
            details E
            L = {1,-2,3,-4}
            E1 = twist(E,L)
            details E1
    Caveat
        The ordering of the list @TT "L"@ must correspond to the ordering of the rays of the fan as taken by @TO "NormalToricVaraieties::NormalToricVarieties"@.
    SeeAlso
        weilToCartier
        cartierIndex
        details
///

doc ///
    Key
        weilToCartierKaneyama
        (weilToCartierKaneyama,List,Fan)
    Headline
        the line bundle given by a Cartier divisor
    Usage
        E = weilToCartier(L,F)
    Inputs
        L:List
        F:Fan
            a pure and full dimensional fan
    Outputs
        E:{ToricVectorBundleKaneyama, ToricVectorBundle}
    Description
        Text
            @TT "L"@ must a list of weights, exactly one for each ray of the fan. Then the list of
            weights for each ray describes a Weil divisor on the toric variety. If the Weil divisor
            defined by these weights defines in fact a Cartier divisor, then @TT "weilToCartier"@
            computes the toric vector bundle associated to the Cartier divisor.
        Text
            If no further options are given then the resulting bundle will be in Klyachko's
            description:
        Example
            F = hirzebruchFan 3
            E =weilToCartier({1,-3,4,-2},F)
            details E
        Text
            If the option @TT "\"Type\" => \"Kaneyama\""@ is given then the resulting bundle will be
            in Kaneyama's description:
        Example
            F = hirzebruchFan 3
            E =weilToCartier({1,-3,4,-2},F,"Type" => "Kaneyama")
            details E
    Caveat
        The ordering of the list @TT "L"@ must correspond to the ordering of the rays of the fan
        output by @TO raySortOfFan@.
    SeeAlso
        cartierIndex
///

doc ///
    Key
        ToricVectorBundleMap
    Headline
        the class of all maps between toric vector bundles
    Description
        Text
	    Let $\mathcal{E}_1$ and $\mathcal{E}_2$ be @TO ToricVectorBundle@s on
	    a common base toric variety$X$. A bundle map is a
	    map $f : \mathcal{E}_1 \to \mathcal{E}_2$ such that for each ray $\rho$ at every step $i$ of the filtration $f(E_1^\rho(i))\subseteq E_2^\rho(i)$.
        Text
	    To specify a map of toric vector bundles, the target and source
	    complexes need to be specified as well as a matrix which
	    is the map between the fibers at the identity point of $E_1$ and $E_2$.
	Text
	    The primary constructor of a toric vecetor bundle map is
	    @TO (map, ToricVectorBundle, ToricVectorBundle, Matrix)@.
    SeeAlso
        map
        source
        target
        isWellDefined
        isIsomorphism
        isInjective
        isSurjective
///

*-
-----------------------------------------------------------
-- Documentation for everything related to maps (29/9/2026)
-----------------------------------------------------------
doc ///
    Key
        isInjective(ToricVectorBundleMap)
    Headline
        test whether a map of toric vector bundles is injective
    Usage
        isInjective f
    Inputs
        f : ToricVectorBundleMap
    Outputs
        : Boolean
            whether f is injective
    Description
        Text
        Determines whether the map @TT "f"@ is injective as a map of
        toric vector bundles.
        The method first checks that @TT "f"@ is well defined and that
        its underlying map of modules is injective. It then checks the
        dimensions of the filtered pieces of the source and target for
        every ray of the underlying toric variety.

        Returns @TT "true"@ if all these conditions are satisfied, and
        @TT "false"@ otherwise.
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 1);
        F = trivialBundle(X, 2);
        f = map(F, E, matrix(ring E,{{1}}));
        assert(not isInjective f)
    SeeAlso
        kernel(ToricVectorBundleMap)
        ToricVectorBundle
///

doc ///
    Key
        isSurjective(ToricVectorBundleMap)
    Headline
        test whether a map of toric vector bundles is surjective
    Usage
        isSurjective f
    Inputs
        f : ToricVectorBundleMap
    Outputs
        : Boolean
            whether f is surjective
    Description
        Text
        Determines whether the map @TT "f"@ is surjective as a map of
        toric vector bundles.

        The method first checks that @TT "f"@ is well defined and that
        its underlying map of modules is surjective. It then checks the
        dimensions of the filtered pieces of the source and target for
        every ray of the underlying toric variety.

        Returns @TT "true"@ if all these conditions are satisfied, and
        @TT "false"@ otherwise.
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 2);
        F = trivialBundle(X, 1);
        f = map(F, E, matrix(ring E,{{1,0}}));
        assert(isSurjective f)
    SeeAlso
        image(ToricVectorBundleMap)
        cokernel(ToricVectorBundleMap)
        ToricVectorBundle
///

doc ///
    Key
        image(ToricVectorBundleMap)
    Headline
        image of a map of toric vector bundles
    Usage
        image f
    Inputs
        f : ToricVectorBundleMap
    Outputs
        : ToricVectorBundle
            the image toric vector bundle of f
    Description
        Text
        Given a map @TT "f : E_1 -> E_2"@ of toric vector bundles,
        computes the image of @TT "f"@ as a toric vector bundle on
        the same toric variety.

        The image is computed by taking the images of the filtered
        pieces of @TT "E_1"@ under the underlying module map of
        @TT "f"@. The resulting filtration data is refined using an
        adapted basis and used to construct the image toric vector
        bundle.
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 1);
        F = trivialBundle(X, 2);
        f = map(E, F, matrix(ring E,{{1,0}}));
        image f
    SeeAlso
        isSurjective(ToricVectorBundleMap)
        isWellDefined(ToricVectorBundleMap)
        ToricVectorBundle
///

doc ///
    Key
        kernel(ToricVectorBundleMap)
    Headline
        kernel of a map of toric vector bundles
    Usage
        kernel f
    Inputs
        f : ToricVectorBundleMap
    Outputs
        : ToricVectorBundle
            the kernel toric vector bundle of f
    Description
        Text
        Given a map @TT "f : E_1 -> E_2"@ of toric vector bundles,
        computes the kernel of @TT "f"@ as a toric vector bundle on
        the same toric variety.

        The kernel is computed from the kernel of the underlying module
        map together with the induced filtrations on the kernel for
        each ray of the toric variety. The resulting filtration data
        is refined using an adapted basis before constructing the
        toric vector bundle.
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 2);
        F = trivialBundle(X, 1);
        f = map(F, E, matrix(ring E,{{1,0}}));
        kernel f;
    SeeAlso
        isInjective(ToricVectorBundleMap)
        isWellDefined(ToricVectorBundleMap)
        ToricVectorBundle
///

doc ///
    Key
        cokernel(ToricVectorBundleMap)
    Headline
        cokernel of a map of toric vector bundles
    Usage
        cokernel f
    Inputs
        f : ToricVectorBundleMap
    Outputs
        : ToricVectorBundle
            the cokernel toric vector bundle of f
    Description
        Text
        Given a map @TT "f : E_1 -> E_2"@ of toric vector bundles,
        computes the cokernel of @TT "f"@ as a toric vector bundle
        on the same toric variety.

        The cokernel is computed from the cokernel of the underlying
        module map together with the filtered pieces associated to the
        rays of the toric variety. The resulting filtration data is
        adapted to produce a toric vector bundle.
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 2);
        F = trivialBundle(X, 1);
        f = map(F, E, matrix(ring E,{{1,0}}));
        cokernel f;
    SeeAlso
        isSurjective(ToricVectorBundleMap)
        isWellDefined(ToricVectorBundleMap)
        ToricVectorBundle
///

doc ///
    Key
        ToricVectorBundleMap ++ ToricVectorBundleMap
    Headline
        direct sum of maps of toric vector bundles
    Usage
        f ++ g
    Inputs
        f : ToricVectorBundleMap
        g : ToricVectorBundleMap
    Outputs
        : ToricVectorBundleMap
            the direct sum of the maps f and g
    Description
        Text
        Given two maps of toric vector bundles @TT "f"@ and @TT "g"@ with the same 
        source and target respectively, returns the map that is the 
        direct sum of @TT "f"@ and @TT "g"@. Its source and target is the same 
        as that of @TT "f"@ and @TT "g"@, and its underlying map is the direct sum 
        of map of vector spaces. 
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 1);
        F = trivialBundle(X, 1);
        f = map(F, E, matrix(ring E,{{1}}));
        g = map(F, E, matrix(ring E,{{2}}));
        f ++ g;
    SeeAlso
        ToricVectorBundleMap
///

doc ///
    Key
        ToricVectorBundleMap ** ToricVectorBundleMap
    Headline
        tensor product of maps of toric vector bundles
    Usage
        f ** g
    Inputs
        f : ToricVectorBundleMap
        g : ToricVectorBundleMap
    Outputs
        : ToricVectorBundleMap
            the tensor product of the maps f and g
    Description
        Text
        Given two maps of toric vector bundles @TT "f"@ and @TT "g"@ with the same 
        source and target respectively, returns the map that is the 
        tensor product of @TT "f"@ and @TT "g"@. Its source and target is the same 
        as that of @TT "f"@ and @TT "g"@, and its underlying map is the tensor 
        product of map of vector spaces. 
    Example
        X = toricProjectiveSpace 2;
        E = trivialBundle(X, 1);
        F = trivialBundle(X, 1);
        f = map(F, E, matrix(ring E,{{1}}));
        g = map(F, E, matrix(ring E,{{2}}));
        f ** g;
    SeeAlso
        ToricVectorBundleMap
///


-------------------------------------------
-- documentation for Weil decorations 
-------------------------------------------
doc ///
    Key
        WeilDecoration
    Headline
        the class of all Weil decorations
    Description
        Text
            A Weil decoration of a toric vector bundle, in the sense of Altmann, Hochenegger and Witt.
        Text
            Consider a toric variety $X$ and a toric vector bundle $E$ on $X$,
            A Weil deocration is a map $\mathcal{D}\colon E_0\to \operatorname{Div}\cup\{\infinity\}$, where $E_0$ denotes the fibre at the origin, such that 
            $1.$ $\mathcal{D}(e) = (\infinity)$ if and only if $e = 0$, and $\mathcal{D}|_{E_0\{0}}$ factorises over the projectivisation \mathbb{P}(E_0)$ of $E_0$.
            $2.$  for all $e, e'\in E_0$, the inequality $\mathcal{D}(e+e')\geq \mathcal{D}(e)\wedge\mathcal{D}(e')$ holds true.
        Text
            The map $\mathcal{D}$ is constant on the strata $E_{\geq D}:=\{e\in E_0|\mathcal{\D}(e)\geq D\}$. Indeed, it sends $e$ to the largest 
            torus-invariant Weil divisor $D$ with e in $E_{>= D}$. 
        Text
            The Weil decoration map is stored as a hash table that associates to a stratum closure the divisor decorating it. 
            The $0$-subspace decorated by $(\infinity)$ is omitted for convenience.
        Example
            M = toricProjectiveSpace 2;
            V = tangentBundle;
            W = weilDecoration V;
            netList strata W
    SeeAlso
        weilDecoration
        net (WeilDecoration)
        variety (WeilDecoration)
        rank (WeilDecoration)
        strata (WeilDecoration)
        weilDecorationDivisors
        weilToKlyachko

///
