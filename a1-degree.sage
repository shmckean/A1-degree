# Implementation of Bezoutian formula for local and global A^1-degrees.
# Currently does not work with R or C, but these can be approximated by the algebraic reals k = AA and algebraic numbers k = QQbar, respectively.
# Written by Thomas Brazelton, Stephen McKean, and Sabrina Pauli.
# We thank Irena Swanson for suggesting a fix to the local calculation, as well as Kyle Ormsby for communicating this suggestion to us.

# Example set-up for number fields.
# The following 2 lines should replace "k = QQ; # INPUT:..."
# s = polygen(QQ,'s');
# k.<sqrt2> = NumberField(s^2-2);

# For univariate polynomials, set n = 2 and use x[1] as a dummy function: f = (f(x[0]),x[1]).

####################

k = QQ; # INPUT: choose field
n = 2;  # INPUT: choose number of variables and polynomials

R = PolynomialRing(k,n,'x');
x = R.gens();

f = ((x[0]-1)*x[0]*x[1],2*x[0]^2-3*x[1]^2); # INPUT: choose morphism; variables indexed from 0 to n-1
p = (x[0]-1,2-3*x[1]^2); # INPUT: choose local point; set p = (1) for global computation

# INPUT: decide how you would like the A^1-degree to be presented:
gram = False; # INPUT: True prints out Gram matrix of A^1-degree
diagonal = False; # INPUT: True prints out A^1-degree as diagonal quadratic form (does not work in characteristic 2)
reduce_over_Q = True; # INPUT: True prints out A^1-degree in hyperbolic and non-hyperbolic parts (reduced over QQ)
details = False; # INPUT: True prints out invariants of bilinear form

####################

# Turn a diagonal matrix into a list of its diagonal entries
def diagonal_matrix_to_list(M):
    list_of_entries = []
    for i in range(0,M.nrows()):
        list_of_entries.append(M[i,i])
    return(list_of_entries)

# Find the squarefree part of an integer
def strip_squares_integer(n):
    factorization = list(factor(n))
    reduced_factorization = []
    for pair in factorization:
        newpower = pair[1] % 2
        reduced_factorization.append([pair[0],newpower])

    m = factor(n).unit()
    for pair in reduced_factorization:
        m = m*(pair[0]**pair[1])
    return(m)

# Find a rational number modulo squares 
def strip_squares_rational(q):
    a = q.numerator()
    b = q.denominator()
    n = a*b
    return strip_squares_integer(n)

# Match elements with their negatives into hyperbolic forms
def hyp_list(list_of_diagonal_entries):
    how_many_hyperbolics = 0
    leftover_stuff = []
    while list_of_diagonal_entries:
        x = list_of_diagonal_entries[0]
        y = -x
        if y in list_of_diagonal_entries:
            how_many_hyperbolics = how_many_hyperbolics + 1

            # Remove y from list
            del list_of_diagonal_entries[list_of_diagonal_entries.index(y)]
        else:
            leftover_stuff.append(x)
        # Remove x from list
        del list_of_diagonal_entries[0]

    if how_many_hyperbolics > 0 and len(leftover_stuff) > 0:
        return('Rational reduction: ' +str(how_many_hyperbolics) + 'H + < ' + ', '.join(map(str,leftover_stuff)) + ' >')
    elif how_many_hyperbolics == 0 and len(leftover_stuff) > 0:
        return('Rational reduction: < ' + ', '.join(map(str,leftover_stuff)) + ' >')
    elif how_many_hyperbolics > 0 and len(leftover_stuff) == 0:
        return('Rational reduction: ' +str(how_many_hyperbolics) + 'H')
    else:
        return('0')

# Take a diagonal matrix over Q and output its hyperbolic parts
def reduce_matrix(M):
    list_of_entries = diagonal_matrix_to_list(M)
    reduced_list_of_entries = []
    for q in list_of_entries:
        w = strip_squares_rational(q)
        reduced_list_of_entries.append(w)
    return(hyp_list(reduced_list_of_entries))

# Cannot diagonalize quadratic form in characteristic 2
if diagonal and k.characteristic() == 2:
    diagonal = False;
    print('cannot diagonalize in characteristic 2')

# Computes Bezoutian polynomial
Rxy = PolynomialRing(k,n,var_array=['X','Y']);
L = Rxy.gens();
X = [L[2*i] for i in range(n)];
Y = [L[2*i+1] for i in range(n)];
W = X.copy();
Z = [X];
for i in range(n): # Z[i] = [Y[0],...,Y[i-1],X[i],...,X[n-1]]
    W = W.copy();
    W[i] = Y[i];
    Z.append(W);
D = [];
for i in range(n):
    for j in range(n):
        D.append((f[i](Z[j])-f[i](Z[j+1]))/(X[j]-Y[j]));
Bez = matrix(Rxy,n,D).det();

# Computes ideal to quotient by in k[X,Y]
I = R.ideal(f);
Sat = I.saturation(R.ideal(p))[0];
if R.ideal(p).is_trivial(): # Ideal needs no modification for global A^1-degree
    g = f;
else: # Use saturation to identify extra relations coming from localization
    J = I.quotient(Sat);
    g = J.gens();
F = [];
for i in range(n):
    F.append(g[i](X));
    F.append(g[i](Y));
J = F*Rxy;

# Computes quotient of Bezoutian and basis of quotient ring
Q = Rxy.quo(J);
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

# Computes Bezoutian bilinear form
m = len(a);
B = [];
for i in range(m):
    for j in range(m):
        if not (ax[i]*ay[j]).is_constant(): # runs through non-constant monomial basis elements
            B.append(Bez.monomial_coefficient(ax[i]*ay[j]));
        else: # picks up constant monomial basis element, scales to equal 1 (one could also just append 1)
            B.append(Bez.constant_coefficient()/(ax[i]*ay[j]));
M = matrix(k,m,B);

# Print whether degree is local or global
if R.ideal(p).is_trivial():
    print('Global A^1-degree of',f,':')
else:
    print('Local A^1-degree of',f,'at',p,':')

# Print A^1-degree as Gram matrix
if gram:
    print(M)
    print('element of GW(',k,')')

# Print A^1-degree as diagonal quadratic form
if diagonal:
    print(2*QuadraticForm(M).rational_diagonal_form())

# Print A^1-degree in terms of hyperbolic forms and standard generators
if reduce_over_Q:
	QMat = 2*QuadraticForm(M).rational_diagonal_form()
	MMat = QMat.Gram_matrix()
	print(reduce_matrix(MMat))

# Print field invariants of bilinear form
if details:
    print('rank',m)
    if k.characteristic() > 0:
        if M.determinant().is_square():
            print('disc','1')
        else:
            print('disc','-1')
    if k.characteristic() == 0:
        print('sign',QuadraticForm(M).signature())

    # Over QQ, print non-trivial Hasse-Witt invariants for first 1000 primes
    if k == QQ:
        print('prime:','Hasse-Witt invariant:')
        for q in primes_first_n(1000):
            if not QuadraticForm(M).hasse_invariant(q) == 1:
                print(q,QuadraticForm(M).hasse_invariant(q))
