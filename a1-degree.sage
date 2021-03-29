# Implementation of Bezoutian formula for local and global A^1-degrees.
# Currently does not work with R or C, but these can be approximated by the algebraic reals k = AA and algebraic numbers k = QQbar, respectively.
# Written by Thomas Brazelton, Stephen McKean, and Sabrina Pauli.

# Example set-up for number fields. 
# The following 2 lines should replace "k = QQ; # INPUT:..."
# s = polygen(QQ,'s');
# k.<sqrt2> = NumberField(s^2-2);

# For univariate polynomials, set n = 2 and use x[1] as a dummy function: f = (f(x[0]),x[1]).




k = QQ; # INPUT: choose field
n = 2;  # INPUT: choose number of variables and polynomials

R = PolynomialRing(k,n,'x');
x = R.gens();

f = ((x[0]-1)*x[0]*x[1],2*x[0]^2-3*x[1]^2); # INPUT: choose morphism; variables indexed from 0 to n-1
p = (x[0]-1,2-3*x[1]^2); # INPUT: choose local point; set p = (1) for global computation
diagonal = True; # INPUT: True prints out diagonal form (does not work in characteristic 2)
details = False; # INPUT: True prints out invariants of bilinear form




if k.characteristic() == 2: # (note: cannot diagonalize quadratic form in characteristic 2)
    diagonal = False;
    print('cannot diagonalize in characteristic 2')

g = []; # (note: reduces f for quotient and basis in local case)
for i in range(n):
    H = [];
    for h in f[i].factor():
        if h[0]^h[1] in R.ideal(p):
            H.append(h[0]^h[1]);
    g.append(prod(H));

Rxy = PolynomialRing(k,n,var_array=['X','Y']); # (note: computes Bezoutian)
L = Rxy.gens();
X = [L[2*i] for i in range(n)];
Y = [L[2*i+1] for i in range(n)];
W = X.copy();
Z = [X];
for i in range(n):
    W = W.copy();
    W[i] = Y[i];
    Z.append(W);
D = [];
for i in range(n):
    for j in range(n):
        D.append((f[i](Z[j])-f[i](Z[j+1]))/(X[j]-Y[j]));
Bez = matrix(Rxy,n,D).det();

F = []; # (note: computes ideals in k[x] and k[X,Y])
for i in range(n):
    F.append(g[i](X));
    F.append(g[i](Y));
J = F*Rxy;

Q = Rxy.quo(J); # (note: computes basis via Bezoutian)
Bez = Q(Bez).lift();
U = [];
Ux = [];
Uy = [];
for i in range(n):
    U.append(x[i]);
    U.append(1);
    Ux.append(X[i]);
    Ux.append(1);
    Uy.append(Y[i]);
    Uy.append(1);
a = [];
ax = [];
ay = [];
for u in Bez.monomials():
    if u(U) not in a:
        a.append(u(U));
        ax.append(u(Ux));
        ay.append(u(Uy));
m = len(a);

B = [];
for i in range(m):
    for j in range(m):
        if not (ax[i]*ay[j]).is_constant(): # (note: runs through non-constant monomial basis elements)
            B.append(Bez.monomial_coefficient(ax[i]*ay[j]));
        else:
            B.append(Bez.constant_coefficient()/(ax[i]*ay[j]));
M = matrix(k,m,B);
if R.ideal(p).is_trivial():
    print('Global A^1-degree of',f)
else:
    print('Local A^1-degree of',f,'at',p)

if diagonal: # (note: prints diagonal form)
    print(QuadraticForm(M).rational_diagonal_form())
else:
    print(M)
    print('element of GW(',k,')')

if details: # (note: prints relevant invariants)
    print('rank',m)
    if k.characteristic() > 0:
        if M.determinant().is_square():
            print('disc','1')
        else:
            print('disc','-1')
    if k.characteristic() == 0:
        print('sign',QuadraticForm(M).signature())
    if k == QQ: # (note: prints Hasse-Witt invariants for k = QQ)
        print('prime:','Hasse-Witt invariant:')
        print('infty',QuadraticForm(M).hasse_invariant(-1)) # (note: prints Hasse-Witt invariant at infinite place)
        for q in primes_first_n(1000): # (note: prints non-trivial Hasse-Witt invariants for first 1000 primes)
            if not QuadraticForm(M).hasse_invariant(q) == 1:
                print(q,QuadraticForm(M).hasse_invariant(q))
