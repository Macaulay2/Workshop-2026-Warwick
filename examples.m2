uninstallPackage "ComprehensiveGBs"
restart
installPackage "ComprehensiveGBs"

--basic example, one polynomial
R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {a*x + b*y}
CGBMain(F, {})
CGB(F)

debug ComprehensiveGBs

--example 9
R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
G = CGBMain(F, {});
G_1

--example on graph=triangle
E={(1,2),(1,3),(2,3)}
V={1,2,3}
G={V,E}
(F,GG)=cgbOnGraph(G,2)
netList cgbOnGraph(G,2) 


--example on graph=square
E={(1,2),(1,3),(3,4),(2,4)}
V={1,2,3,4}
G={V,E}
(F,GG)=cgbOnGraph(G,2);
netList for i in GG list i_{0,1} --showing only the segment's parameters



