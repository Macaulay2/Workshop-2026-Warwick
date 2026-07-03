---------------------------------------------
--Comprehensive Groebner Basis in Macaulay2: 
---------------------------------------------

installPackage "ComprehensiveGBs"

-- No more big coefficients in the strata   (these where coming from the GB implementation in M2, 
--                                          which tries to avoid denominatoris when possible)
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
G = CGBMain(F, {});
netList for g in G list {g_0, factor g_1}

-- A *LOT* of redundant strata (where the CGB identically vanishes).. 
-- So we added strata reduction!
G = CGBMain(F, {}, ReduceStrata => true);
netList for g in G list {g_0, factor g_1}

-- For this, at each step we have to check ideal membership 
-- (i.e. do all leading coefficients of the GB vanish on the strata?), 
-- and using the Rabinowitsch trick can make everything faster                                      -- (i.e. to check f in <E>, test 1 in <E, y*f-1>)
benchmark "G = CGBMain(F, {}, ReduceStrata => true, Strategy => \"radical\", Verbose => false)"
benchmark "G = CGBMain(F, {}, ReduceStrata => true, Strategy => \"Rabinowitsch\", Verbose => false)"
-- And we were more careful with cacheing rings.

-- Dulcis in fundu: we have some DOCUMENTATION!
viewHelp ComprehensiveGBs
*-

end









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
elapsedTime G = CGBMain(F, {});
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
