---------------------------------------------
--Comprehensive Groebner Basis in Macaulay2: 
---------------------------------------------

installPackage "ComprehensiveGBs"

-- No more big coefficients in the strata   (these where coming from the GB implementation in M2, 
--                                          which tries to avoid denominatoris when possible)
U = QQ[a,b]
R = U[x,y,z, MonomialOrder => GRevLex]
F = {x^3 - a, y^4 - b, x+y-z}
G = CGBMain(F, {});
L = PGBMain(CGBFromTriple({{0_U}, {1_U}, F}))

netList for g in G list {g_0, factor g_1}
netList L

-- A *LOT* of redundant strata (where the CGB identically vanishes).. 

-- So we added strata reduction!
G = CGBMain(F, {}, ReduceStrata => true);
netList for g in G list {g_0, factor g_1}


-- For this, at each step we have to check ideal membership 
-- (i.e. do all leading coefficients of the GB vanish on the strata?), 
-- and using the Rabinowitsch trick can make everything faster                                      -- (i.e. to check f in <E>, test 1 in <E, y*f-1>)
print("Radical :", benchmark "G = CGBMain(F, {}, ReduceStrata => true, Strategy => \"radical\", Verbose => false)")
print("Rabinowitsch:", benchmark "G = CGBMain(F, {}, ReduceStrata => true, Strategy => \"Rabinowitsch\", Verbose => false)")
-- And we were more careful with cacheing rings.

-- Dulcis in fundu: we have some DOCUMENTATION!
viewHelp ComprehensiveGBs
*-

end


R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
G = CGBMain(F, {}, ReduceStrata => true);
netList for g in G list {g_0, factor g_1}

-- strata reduction
G = CGBMain(F, {}, ReduceStrata => true);
netList for g in G list {g_0, factor g_1}

-- Some options for Depth
G0 = CGBMain(F, {}, Depth => 0);
netList for g in G0 list {g_0, factor g_1}
G0' = CGBMain(F, {}, Depth => 0, ReduceStrata => true);
netList for g in G0' list {g_0, factor g_1}


G1 = CGBMain(F, {}, Depth => 1);
netList for g in G1 list {g_0, factor g_1}
G1' = CGBMain(F, {}, Depth => 1, ReduceStrata => true);
netList for g in G1' list {g_0, factor g_1}


G2 = CGBMain(F, {}, Depth => 2);
netList for g in G2 list {g_0, factor g_1}
G2' = CGBMain(F, {}, Depth => 2, ReduceStrata => true);
netList for g in G2' list {g_0, factor g_1}










uninstallPackage "ComprehensiveGBs"
restart
installPackage "ComprehensiveGBs"

viewHelp ComprehensiveGBs


--basic example, one polynomial
R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {a*x + b*y}
CGBMain(F, {})
CGB(F)




--example 9
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
elapsedTime G = CGBMain(F, {}, Verbose => false);
#G

elapsedTime G = CGBMain(F, {}, ReduceStrata => true, Verbose => true);
#G

elapsedTime G = CGBMain(F, {}, ReduceStrata => true, Strategy => "Rabinowitsch", Verbose => false);
benchmark "G = CGBMain(F, {}, ReduceStrata => true, Strategy => \"radical\", Verbose => false)"

#G


G_1
G_2
G_3
debug ComprehensiveGBs

-- list of strata
netList for g in G list {g_0, factor g_1}


--example on graph=triangle
E={(1,2),(1,3),(2,3)}
V={1,2,3}
G={V,E}
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
elapsedTime G = CGBMain(F, {});
-- 236.631s elapsed
#G --=230


--SS example 3
R = QQ[a,b,c,d][x_1,x_2,y_1,y_2,s, MonomialOrder => Lex]
f=a*x_1^2+b*y_1
g=c*y_2^2+d*x_2
F = {f,g,(x_1-x_2)^2+(y_1-y_2)^2-s,diff_(x_1) f * diff_(y_2) g -diff_(y_1) f * diff_(x_2) g, diff_(x_1) f * (y_1-y_2) - diff_(y_1) f * (x_1-x_2)}
elapsedTime G = CGBMain(F, {}, Strategy =);
 -- 1255.88s elapsed
#G --=1637

--SS example 4
R = QQ[a,b,c,e][x_1,x_2,y_1,y_2, MonomialOrder => Lex]
f=x_1^2+y_1^2+a
g=y_2-b*x_2^2+c
F = {f,g}
G = CGBMain(F, {});


--SS example 5 (40s)
R = QQ[a,b][x,y,z,s, MonomialOrder => Lex]
f=(x-a)^2+b*y^2+b
F = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
elapsedTime G = CGBMain(F, {});
#G
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
elapsedTime GG = CGBMain(F, {});
#GG

--Examples from Game Theory
U = QQ[a_{1,1}..a_{2,2}]
R = U[p_{1,1}..p_{2,2}]
M1 = matrix({
    {p_{1,1}+p_{1,2}, a_{1,1}*p_{1,1}+ a_{1,2}*p_{1,2}}, 
    {p_{2,1}+ p_{2,2}, a_{2,1}*p_{2,1}+ a_{2,2}*p_{2,2}}})

M2 = matrix({
    {p_{1,1}+p_{2,1}, a_{1,1}*p_{1,1}+ a_{2,1}*p_{2,1}}, 
    {p_{1,2}+ p_{2,2}, a_{1,2}*p_{1,2}+ a_{2,2}*p_{2,2}}})

F = {det M1, det M2};
L = CGBMain(F, ReduceStrata => true);
netList for l in L list {l_0, l_1};

U = QQ[a_{1,1}..a_{2,2}, b_{1,1}..b_{2,2}]
R = U[p_{1,1}..p_{2,2}]

M1 = matrix({
    {p_{1,1}+p_{1,2}, a_{1,1}*p_{1,1}+ a_{1,2}*p_{1,2}}, 
    {p_{2,1}+ p_{2,2}, a_{2,1}*p_{2,1}+ a_{2,2}*p_{2,2}}})

M2 = matrix({
    {p_{1,1}+p_{2,1}, b_{1,1}*p_{1,1}+ b_{2,1}*p_{2,1}}, 
    {p_{1,2}+ p_{2,2}, b_{1,2}*p_{1,2}+ b_{2,2}*p_{2,2}}})

F = {det M1, det M2} -- Defining equations for the Sphon variety of a 2x2 game with payoff matrices A= (a_{i, j}) and B = (b_{i,j})

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
T = CGBFromTriple({{0_U}, {1_U}, F})
L= PGBMain(T)
netList oo

LL = apply(CGBMain(F, {}, ReduceStrata => true), e -> toList e)
netList oo


---------------------------
-- TODO:
-- try examples of generic initial ideal 'gin'?
-- recursion depth limit
-- How big can we go?
>>>>>>> 527bfb3 (add todos)
