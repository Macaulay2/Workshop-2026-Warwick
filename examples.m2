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

--example 4
R = QQ[a,b,c,e][x_1,x_2,y_1,y_2, MonomialOrder => Lex]
f=x_1^2+y_1^2+a
g=y_2-b*x_2^2+c
F = {f,g}
G = CGBMain(F, {});
G_1

--example 5 (40s)
R = QQ[a,b][x,y,z,s, MonomialOrder => Lex]
f=(x-a)^2+b*y^2+b
F = {f-z,x^2+y^2+z^2-s,x+z*diff(x, f),y+z*diff(y, f)}
elapsedTime G = CGBMain(F, {});
#G
netList for j from 0 to 9 list (G_j)_{0,1}

