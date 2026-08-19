--profile method() ---->> Gives a count of called functions and elapsed time

end 
restart
installPackage "ComprehensiveGBs"
load "consistency.m2"
---------------------
--TEST
---------------------
U = QQ[a, b, c, MonomialOrder => Lex]
R = U[x,y,z, MonomialOrder => Lex];
G = {a*x*y + b*x, b*x^2*y+c*z, a*b*x+a*x*y+z, a*y+z, c*x + c*z^2}
T = CGBFromTriple({{0_U}, {1_U}, G})
L= PGBMain(T)
matrix {MDBasis(G)} == matrix {{a*y + z, c*x + c*z^2}}
assert({a*y + z, c*x + c*z^2} == MDBasis(G));

--Example 9
U = QQ[a, b, c]
R = U[x,y,z]
F = {x^3 - a, y^4 - b, x+y-z}
T = CGBFromTriple({{0_U}, {1_U}, F})
L= PGBMain(T)

U = QQ[a,b]
R = U[x,y, MonomialOrder => Lex]
F = {a*x + b*y}
T = CGBFromTriple({{0_U}, {1_U}, F})
L =PGBMain(T)

U = QQ[a,b]
R = U[x,y,z]
F = {x^3 - a, y^4 - b, x+y-z}
T = CGBFromTriple({{0_U}, {1_U}, F})
L = PGBMain(T)
LL = CGBMain(F, {}, Verbose => false);


consistent = method();
consistent (List, List) := (E, N) ->(
    if length E == 0 then (
        if length N == 0 then (
            return false
        );
        R := ring N_0;
        I := ideal 0_R;
    ) else (
        I := radical (ideal E);
    );
    
    return not(isEmpty(select(N, n -> not(isMember(n, I)))))
);
