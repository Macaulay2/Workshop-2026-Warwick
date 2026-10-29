---------------------------------------------
--Comprehensive Groebner Basis in Macaulay2: 
---------------------------------------------

installPackage "ComprehensiveGBs"

-- No more big coefficients in the strata   (these where coming from the GB implementation in M2, 
--                                          which tries to avoid denominatoris when possible)
U = QQ[a,b]
R = U[x,y,z, MonomialOrder => GRevLex]
F = {x^3 - a, y^4 - b, x+y-z}
G = cgbMain F;
L = pgbMain cgbFromTriple {{0_U}, {1_U}, F}

netList for g in G list {g_0, factor \ g_1}
netList L

-- A *LOT* of redundant strata (where the CGB identically vanishes).. 

-- So we added strata reduction!
G = cgbMain(F, ReduceStrata => true);
netList for g in G list {g_0, factor \ g_1}


-- For this, at each step we split V(S + h_i) into irreducible components,
-- and skip those already covered by the strata computed so far.
-- print("ReduceStrata:", benchmark "G = cgbMain(F, ReduceStrata => true, Verbose => false)")
-- And we were more careful with cacheing rings.

-- Dulcis in fundu: we have some DOCUMENTATION!
viewHelp ComprehensiveGBs

end


R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
G = cgbMain(F, ReduceStrata => true);
netList for g in G list {g_0, factor \ g_1}

-- strata reduction
G = cgbMain(F, ReduceStrata => true);
netList for g in G list {g_0, factor \ g_1}

-- Some options for Depth
G0 = cgbMain(F, Depth => 0);
netList for g in G0 list {g_0, factor \ g_1}
G0' = cgbMain(F, Depth => 0, ReduceStrata => true);
netList for g in G0' list {g_0, factor \ g_1}


G1 = cgbMain(F, Depth => 1);
netList for g in G1 list {g_0, factor \ g_1}
G1' = cgbMain(F, Depth => 1, ReduceStrata => true);
netList for g in G1' list {g_0, factor \ g_1}


G2 = cgbMain(F, Depth => 2);
netList for g in G2 list {g_0, factor \ g_1}
G2' = cgbMain(F, Depth => 2, ReduceStrata => true);
netList for g in G2' list {g_0, factor \ g_1}


R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {x*2 + y*2-1, (x-a)^2+(x-b)^2-1}
cgbMain F







uninstallPackage "ComprehensiveGBs"
restart
installPackage "ComprehensiveGBs"

viewHelp ComprehensiveGBs


--basic example, one polynomial
R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {a*x + b*y}
cgbMain F
cgb F
Lrestricted = cgbMain(F, {a});
U = QQ[a,b];
R = U[x];
F = {a*x, a*(a-1)};
cgbMain(F,{b})




--example 9
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
elapsedTime G = cgbMain(F, Verbose => false);
#G

elapsedTime G = cgbMain(F, ReduceStrata => true, Verbose => true);
#G


G_1
G_2
G_3
debug ComprehensiveGBs

-- list of strata
netList for g in G list {g_0, factor \ g_1}


--example on graph=triangle
E={(1,2),(1,3),(2,3)}
V={1,2,3}
G={V,E}
(F,GG)=cgbOnGraph(G,1);
(F,GG)=cgbOnGraph(G,2);

-- strata
netList for g in GG list {g_0, {g_1}}


-- we should get the cgbOnGraph to return just the polys
-- to allow the user to select how they want the CGB alg to run

--example on graph=square
E={(1,2),(1,3),(3,4),(2,4)}
V={1,2,3,4}
G={V,E}
(F,GG)=cgbOnGraph(G,2);
netList for i in GG list i_{0,1} --showing only the segment's parameters


--SS example 2
R = QQ[A,B][X,Y,Z, MonomialOrder => Lex]
F = {X^4-A,Y^5-B,X+Y-Z}
elapsedTime G = cgbMain F;
-- 25.3401s elapsed
#G -- 230
elapsedTime G = cgbMain(F, ReduceStrata => true);
-- 1.56596s elapsed
#G -- 15

--SS example 3
R = QQ[a,b,c,d][x_1,x_2,y_1,y_2,s, MonomialOrder => Lex]
f=a*x_1^2+b*y_1
g=c*y_2^2+d*x_2
F = {f,g,(x_1-x_2)^2+(y_1-y_2)^2-s,diff_(x_1) f * diff_(y_2) g -diff_(y_1) f * diff_(x_2) g, diff_(x_1) f * (y_1-y_2) - diff_(y_1) f * (x_1-x_2)}
elapsedTime G = cgbMain F;
-- 39.6449s elapsed
#G -- 1515
elapsedTime G = cgbMain(F, ReduceStrata => true);
-- 5.2563s elapsed
#G -- 25

--SS example 4
R = QQ[a,b,c,e][x_1,x_2,y_1,y_2, MonomialOrder => Lex]
f=x_1^2+y_1^2+a
g=y_2-b*x_2^2+c
F = {f,g}
G = cgbMain F;


--SS example 5
R = QQ[a,b, MonomialOrder => Lex][x,y,z,s, MonomialOrder => Lex]
f=(x-a)^2+b*y^2+b
F = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
elapsedTime G = cgbMain F;
-- 22.1721s elapsed
#G -- 96
elapsedTime G = cgbMain(F, ReduceStrata => true);
-- 11.337s elapsed
#G -- 35
netList for j from 0 to 9 list (G_j)_{0,1}



-- SS Example 6:

R = QQ[a,b][x, y, z, s, MonomialOrder => Lex]
f = (x - a)^2 + a*y^2 + b
F = {
    f - z,
    x^2 + y^2 + z^2 - s,
    x + diff(x, f)*z,
    y + diff(y, f)*z
    }
elapsedTime GG = cgbMain(F, ReduceStrata => true);
-- 100.895s elapsed
#GG -- 25

--Examples from Game Theory
U = QQ[a_{1,1}..a_{2,2}]
R = U[p_{1,1}..p_{2,2}]
M1 = matrix {
    {p_{1,1}+p_{1,2}, a_{1,1}*p_{1,1}+ a_{1,2}*p_{1,2}}, 
    {p_{2,1}+ p_{2,2}, a_{2,1}*p_{2,1}+ a_{2,2}*p_{2,2}}}

M2 = matrix {
    {p_{1,1}+p_{2,1}, a_{1,1}*p_{1,1}+ a_{2,1}*p_{2,1}}, 
    {p_{1,2}+ p_{2,2}, a_{1,2}*p_{1,2}+ a_{2,2}*p_{2,2}}}

F = {det M1, det M2};
L = cgbMain(F, ReduceStrata => true);
netList for l in L list {l_0, l_1};

U = QQ[a_{1,1}..a_{2,2}, b_{1,1}..b_{2,2}]
R = U[p_{1,1}..p_{2,2}]

M1 = matrix {
    {p_{1,1}+p_{1,2}, a_{1,1}*p_{1,1}+ a_{1,2}*p_{1,2}}, 
    {p_{2,1}+ p_{2,2}, a_{2,1}*p_{2,1}+ a_{2,2}*p_{2,2}}}

M2 = matrix {
    {p_{1,1}+p_{2,1}, b_{1,1}*p_{1,1}+ b_{2,1}*p_{2,1}}, 
    {p_{1,2}+ p_{2,2}, b_{1,2}*p_{1,2}+ b_{2,2}*p_{2,2}}}

F = {det M1, det M2} -- Defining equations for the Sphon variety of a 2x2 game with payoff matrices A= (a_{i, j}) and B = (b_{i,j})
L = cgbMain(F, ReduceStrata => true);
L = cgbMain(F, ReduceStrata => true, Depth => 0);
elapsedTime L = pgbMain(F);


spohnMatrix = method();
spohnMatrix

--Example 6.1 KSW
R = QQ[x,y,a,b,c,
    MonomialOrder => {
        GRevLex => 2,
        GRevLex => 3
    }
];

U = QQ[a,b,c, MonomialOrder => GRevLex]
R = U[x,y, MonomialOrder => GRevLex]

U = QQ[a,b,c, MonomialOrder => Lex]
R = U[x,y, MonomialOrder => Lex]

F={a*x-b,b*y-a,c*x^2-y,c*y^2-x}
T = cgbFromTriple {{0_U}, {1_U}, F}
L= pgbMain T
LL= pgbMain F
netList oo
T = cgbFromTriple {{a,b}, {c}, F};
Lrestricted = pgbMain T;
netList Lrestricted

LL = apply(cgbMain(F, ReduceStrata => true), e -> toList e)
netList oo

----------
--The following are all examples taken from Nabeshima

--Example 4.8
U = QQ[a,b,c, MonomialOrder => Lex]
R = U[x,y, MonomialOrder => Lex]
F={a*x^2+b*y^2,c*x^2+y^2,2*a*x-2*c*y}

--Example F_i, for i=1,2,3,4,5,6,7,8
U = QQ[a,b,c,d, MonomialOrder => Lex]
R = U[x,y,z,w, MonomialOrder => Lex]
F1={a*x^4*y+x*y^2+b*x,x^3+2*x*y,b*x^2+x^2*y}
F2={a*x^2*y^3+b*y+y,x^2*y^2+x*y+2,a*x^2+b*y+2}
F3={a*x^4+c*x^2+b,b*x^3+x^2+2,c*x^2+d*x}
F4={a*x^3*y+c*x*y^2,x^4*y+3*d*y,c*x^2+b*x*y,x^2*y^2+a*x^2,x^5+y^5}
F5={a*x^2*y+b*x+y^3,a*x^2*y+b*x*y,y^2+b*x^2*y+c*x*y}
F6={x^4+a*x^3+b*x^2+c*x+d, 4*x^3+3*a*x^2+2*b*x+c}
F7={x^3 - a, y^4-b, x+y-a*z}
F8={a*x^2+b*y, c*w^2 + z, (x-z)^2 + (y-w)^2, 2*d*x*w - 2*b*y}
--------

--The following are examples from Montes and Recio
U = QQ[a,b, MonomialOrder => Lex]
R = U[x_2, x_3, y_2, y_3, MonomialOrder => GRevLex]
E4 = {(a - 1)*y_2 - b*(x_2 - 1),
     (a - 1)*(x_2 + 1) + b*y_2,
     (a + 1)*y_3 - b*(x_3 + 1),
     (a + 1)*(x_3 - 1) + b*y_3,
     (x_3 - a)^2 + y_3^2 - (x_2 - a)^2 - y_2^2}


U = QQ[a, b, sv, cv, sw, cw, MonomialOrder => Lex]
R = U[x_1, y_1, x_2, y_2, MonomialOrder => GRevLex]
E5 = {(x_1 - a)^2 + (y_1 - 1)^2 - a^2 - 1,
     (x_2 + b)^2 + (y_2 - 1)^2 - b^2 - 1,
     a*(x_1 - a) + (y_1 - 1) + (a^2 + 1)*cv,
     -b*(x_2 + b) + (y_2 - 1) + (1 + b^2)*cw,
     a*(y_1 - 1) - (x_1 - a) + (a^2 + 1)*sv,
     -b*(y_2 - 1) - (x_2 + b) + (b^2 + 1)*sw,
     x_1*y_2 - 2*x_1 - x_2*y_1 + 2*x_2,
     cv^2 + sv^2 - 1,
     cw^2 + sw^2 - 1}

--Examples from KSW (they took the ones from
--Nabeshima and made them more complex)
U = QQ[a,b,c,d, MonomialOrder => Lex] -- (Ollie: Computations finish now with GRevLex - is this order problematic?)
R = U[x,y,z,w, MonomialOrder => Lex]

S1= {a*x^4 + c*x^2 + y,
     b*x^3 + x^2 + 2,
     c*x^2 + d*x + y}


S2= {a*x^3*y + c*x*y^2 + b*x + y,
     x^4*y + 3*d*y,
     c*x^2 + b*x*y,
     x^2*y^2 + a*x^2,
     x^5 + y^5}


S3= {a*x^2*y + b*x^2 + y^3,
     a*x^2*y + b*x*y + c*y^2,
     a*y^3 + b*x^2*y + c*x*y}


S4= {x^4 + a*x^3 + b*x^2 + c*x*y + d,
     4*x^3 + 3*a*x^2*y + 2*b*x + c + y}


S5= {a*x^2 + b*y*z + c*z*w,
     c*w^2 + b*y + z,
     (x-z)^2 + (y-w)^2,
     2*d*x*w - 2*b*y*z}

T1 = cgbFromTriple {{0_U}, {1_U}, S1};
T2 = cgbFromTriple {{0_U}, {1_U}, S2};
T3 = cgbFromTriple {{0_U}, {1_U}, S3};
T4 = cgbFromTriple {{0_U}, {1_U}, S4};
T5 = cgbFromTriple {{0_U}, {1_U}, S5};

elapsedTime pgbMain T1; -- 0.26s
elapsedTime cgb(S1, ReduceStrata => false); -- <0.1s

elapsedTime pgbMain T2; -- 67.06s to 80.12s
elapsedTime pgbMain T3; --  2.63s
elapsedTime pgbMain T4; --  1.24s
elapsedTime pgbMain T5; --  1.74s



-- Example from KSW: "the famous P3P problem
--from computer vision."
U = QQ[p, q, r, a, b, MonomialOrder => Lex];
R = U[x,y, MonomialOrder => GRevLex];

P3P= {(1 - a)*y^2 - a*x^2 - p*y + a*r*x*y +1,
     (1 - b)*x^2 - b*y^2 - q*x + b*r*x*y +1};

T = cgbFromTriple {{0_U}, {1_U}, P3P};
elapsedTime L= pgbMain T; -- 2.00s


--cubic curve example
R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {x^3 + a*x + b - y^2, -2*y, 3*x^2 + a}
G = cgbMain F;
G = cgbMain(F, ReduceStrata => true);
netList G

U = QQ[a, MonomialOrder => Lex];
R = U[x,y, MonomialOrder => Lex];
G = {
    a*x^2-y,
    a*y^2-1,
    a*x-1,
    (a+1)*x-y,
    (a+1)*y-a
    };
M = minimalDicksonBasis G;
netList M


-- in KSW the P3P takes around 2.5s with KSW and 1+hour
-- with SS.


---------------------------
-- TODO:
-- try examples of generic initial ideal 'gin'?
-- recursion depth limit
-- How big can we go?
