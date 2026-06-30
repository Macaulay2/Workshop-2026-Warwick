uninstallPackage "ComprehensiveGBs"
restart
installPackage "ComprehensiveGBs"


R = QQ[a,b][x,y,z, MonomialOrder => Lex]
F = {x^3 - a, y^4 - b, x+y-z}
G = CGBMain(F, {});o
G_1


R = QQ[a,b][x,y, MonomialOrder => Lex]
F = {a*x + b*y}
CGBMain(F, {})

debug ComprehensiveGBs
