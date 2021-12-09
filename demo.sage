# This is a demonstration of a1-degree.sage

##########

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
        return(str(how_many_hyperbolics) + 'H + < ' + ', '.join(map(str,leftover_stuff)) + ' >')
    elif how_many_hyperbolics == 0 and len(leftover_stuff) > 0:
        return('< ' + ', '.join(map(str,leftover_stuff)) + ' >')
    elif how_many_hyperbolics > 0 and len(leftover_stuff) == 0:
        return(str(how_many_hyperbolics) + 'H')
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

def degA1(f,p,R,k,n):
    # Print whether degree is local or global
    if R.ideal(p).is_trivial():
        print('Global A^1-degree of',f,':')
    else:
        print('Local A^1-degree of',f,'at',p,':')
    
    # Add dummy variable for code to run in univariate case
    if n == 1:
        n = 2
        R = PolynomialRing(k,n,'x')
        x = R.gens()
        f = (f(x[0]),x[1])
    
    # Computes Bezoutian polynomial
    x = R.gens()
    Rxy = PolynomialRing(k,n,var_array=['X','Y'])
    L = Rxy.gens()
    X = [L[2*i] for i in range(n)]
    Y = [L[2*i+1] for i in range(n)]
    W = X.copy()
    Z = [X]
    for i in range(n): # Z[i] = [Y[0],...,Y[i-1],X[i],...,X[n-1]]
        W = W.copy()
        W[i] = Y[i]
        Z.append(W)
    D = []
    for i in range(n):
        for j in range(n):
            D.append((f[i](Z[j])-f[i](Z[j+1]))/(X[j]-Y[j]))
    Bez = matrix(Rxy,n,D).det()

    # Computes ideal to quotient by in k[X,Y]
    I = R.ideal(f)
    Sat = I.saturation(R.ideal(p))[0]
    if R.ideal(p).is_trivial(): # Ideal needs no modification for global A^1-degree
        g = f
    else: # Use saturation to identify extra relations coming from localization
        J = I.quotient(Sat)
        g = J.gens()
    F = []
    for i in range(n):
        F.append(g[i](X))
        F.append(g[i](Y))
    J = F*Rxy

    # Computes quotient of Bezoutian and basis of quotient ring
    Q = Rxy.quo(J)
    Bez = Q(Bez).lift()
    U = []
    Ux = []
    Uy = []
    for i in range(n):
        U.append(x[i])
        U.append(1)
        Ux.append(X[i])
        Ux.append(1)
        Uy.append(Y[i])
        Uy.append(1)
    a = []
    ax = []
    ay = []
    for u in Bez.monomials():
        if u(U) not in a:
            a.append(u(U))
            ax.append(u(Ux))
            ay.append(u(Uy))

    # Computes Bezoutian bilinear form
    m = len(a)
    B = []
    for i in range(m):
        for j in range(m):
            if not (ax[i]*ay[j]).is_constant(): # Runs through non-constant monomial basis elements
                B.append(Bez.monomial_coefficient(ax[i]*ay[j]))
            else: # Picks up constant monomial basis element, scales to equal 1 (one could also just append 1)
                B.append(Bez.constant_coefficient()/(ax[i]*ay[j]))
    M = matrix(k,m,B)

    # Output A1-degree
    QMat = QuadraticForm(M).rational_diagonal_form()
    MMat = 2*QMat.Gram_matrix()
    print(reduce_matrix(MMat))

##########

# A1-Euler characteristic of P^n
n = 4;
k = QQ;
R = PolynomialRing(k,n,'x');
x = R.gens();

f = [-1+x[0]*x[n-1]]
for i in range(n-1):
    f.append(-x[i]+x[i+1]*x[n-1])
p = (1);

degA1(f,p,R,k,n)

##########

# A1-Euler characteristic of Gr(2,4)
n = 4;
k = QQ;
R = PolynomialRing(k,n,'x');
x = R.gens();

f = (x[2]-x[0]*x[1],x[3]-x[0]-x[1]^2,1-x[0]*x[3],-x[2]-x[1]*x[3]);
p = (1);

degA1(f,p,R,k,n)

##########

# Trace form of QQ[x]/m(x) over QQ
n = 1;
k = QQ;
R = PolynomialRing(k,n,'x');
x = R.gens();

m = x[0]^3-x[0]^2-2*x[0]-8;
f = m*derivative(m,x[0]);
p = (m);

degA1(f,p,R,k,n)

##########

# Local degree at rational point vs non-rational point
n = 2;
k = QQ;
R = PolynomialRing(k,n,'x');
x = R.gens();

f = ((x[0]-1)*x[0]*x[1],2*x[0]^2-3*x[1]^2);
p = (x[0],x[1]);
q = (x[0]-1,x[1]^2-2/3);

degA1(f,p,R,k,n)
degA1(f,q,R,k,n)
degA1(f,(1),R,k,n)

##########

# Local degree at inseparable point; error: cannot use .saturation() with FunctionField
n = 2;
P = 5;
k.<t> = FunctionField(GF(P));
R = PolynomialRing(k,n,'x');
x = R.gens();

f = (x[0]^P-t,x[0]*x[1]);
p = (x[0]^P-t,x[1]);

degA1(f,p,R,k,n)