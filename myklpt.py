
from sage.all import *

def trysolve(f, y):
    y = ZZ(y)
    assert y > 0
    if y.is_pseudoprime():
        return f.solve_integer(y, algorithm='cornacchia')

##def equivalent_prime_ideal(I):
##    Q = I.quaternion_algebra()
##    N0 = I.norm()
##    L = IntegralLattice(I.gram_matrix()).lll().basis_matrix() * I.basis_matrix()
##    bnd = 1
##    while True:
##        for _ in range(5):
##            δ = Q(sum(randrange(-bnd,bnd+1)*v for v in L))
##            N = ZZ(δ.reduced_norm() / N0)
##            if N.is_pseudoprime():
##                break
##        else:
##            bnd += 1
##            continue
##        break
##    print(f'{δ = }')
##    assert δ in I
##    J = I * (δ.conjugate() / N0)
##    del N0
##    print(f'{I = }')
##    print(f'{N = }')
##    return J

def norm_and_generator(I):
    N = ZZ(I.norm())
    O0 = I.left_order()
    bnd = 1
    while True:
        for _ in range(5):
            α = sum(randrange(-bnd,bnd+1)*b for b in I.basis())
            if gcd(α.reduced_norm(), N**2) == N:
                break
        else:
            bnd += 1
            continue
        break
    else:
        assert False
#    print(f'{α = }')
    assert I == O0*N + O0*α
    return N, α

def represent_integer(O0, rhs):
    Q = O0.quaternion_algebra()
    ii,jj,kk = Q.gens()
    if Q.quaternion_order(Q.basis()).discriminant() != 4 * ii**2 * jj**2:
        raise NotImplementedError
    q, p = ZZ(-ii**2), ZZ(-jj**2)
    nf = BinaryQF(1, 0, q)
    cbnd = isqrt(rhs / 2 / p)
    dbnd = isqrt(rhs / 2 / (p*q))
    if not cbnd or not dbnd:
        return
    for _ in range(999):
        c = randrange(1,cbnd+1)
        d = randrange(1,dbnd+1)
        rhs1 = rhs - p*nf(c,d)

        sol = trysolve(nf, rhs1)
        if sol is not None:
            a,b = sol
            break
    else:
        return
    γ = Q([a,b,c,d])
#    print(f'{γ = }')
    assert γ in O0
    assert γ.reduced_norm() == rhs
    return γ

def ideal_mod_constraint(N, α, γ):
    ii,jj,kk = α.parent().gens()
    mat = matrix(GF(N), [list(elt) for elt in (γ*jj, γ*kk, α, ii*α, jj*α, kk*α)])
    ker = mat.left_kernel_matrix()
    return next(filter(bool, ker[:,:2].change_ring(ZZ)))  #TODO kernel rank > 1?

def strong_approximation(N, α, C, D, rhs):
    ii,jj,kk = α.parent().gens()
    q, p = ZZ(-ii**2), ZZ(-jj**2)
    nf = BinaryQF([1, 0, q])
    rhs1 = Mod(rhs, N) / p / nf(C,D)
    if not rhs1.is_square():
        l = next(l for l in rhs.prime_divisors() if not Mod(l,N).is_square())
        rhs //= l
        rhs1 //= l
        assert rhs1.is_square()
    λ = ZZ(rhs1.sqrt())
    print(f'{λ = }')
    λC,λD = (λ * vector(GF(N), (C,D))).change_ring(ZZ)

    x,y,z,t = polygens(ZZ, 'x,y,z,t')
    eqn = rhs - nf(N*x,N*y) - p*nf(λC+N*z, λD+N*t)
#    print(eqn)
    assert eqn % N == 0
    eqn1 = eqn // N % N
    U, V, W = eqn1[z], eqn1[t], -eqn1.constant_coefficient()
    assert eqn1 == U*z + V*t - W

    # Petit-Smith
    lat = matrix([[U,0,1,0],[V,0,0,1],[-W,1,0,0]]).stack(N*identity_matrix(4))
    scal = diagonal_matrix([N**2, N, 1, 1])
    for row in matrix(ZZ, filter(bool, (lat * scal).LLL() * ~scal)):
#        print(row)
        if row[1] < 0:
            row = -row
        if not row[0] and row[1] == 1:
            sol0 = row[2:]
            break
    else:
        assert False, 'should never happen'
    import fpylll
    mat = matrix(filter(bool, matrix([[V,-U],[N,0],[0,N]]).LLL()))
    assert mat.dimensions() == (2, 2)
    lat = fpylll.IntegerMatrix(2, 2)
    for i,row in enumerate(mat):
        for j,c in enumerate(row):
            lat[i,j] = c
    gso = fpylll.GSO.Mat(lat)  #TODO lengths are slightly off when q>1
    gso.update_gso()
    cnt = 10
    seen = set()
    while True:
        enum = fpylll.Enumeration(gso, cnt, fpylll.EvaluatorStrategy.BEST_N_SOLUTIONS)
        rs = enum.enumerate(0, 2, N**2, 0, tuple(mat.solve_left(sol0)))
        for r in rs:
            z,t = sol0 - vector(ZZ,r[1])*mat
            assert eqn1(0,0,z,t) % N == 0
            if (z,t) in seen:
                continue
            seen.add((z,t))
            assert eqn(0,0,z,t) % N**2 == 0
            rhs2 = ZZ(eqn(0,0,z,t)) // N**2
            sol = trysolve(nf, rhs2)
            if sol is not None:
                x,y = sol
                break
        else:
            if len(rs) < cnt:
                raise NotImplementedError
            cnt *= 2
            continue
        break

    γ = (λC*jj + λD*kk) + N*(x + y*ii + z*jj + t*kk)
#    print(f'{γ = }')
    assert γ.reduced_norm() == rhs
    return γ

def klpt(I, T):
    ii = I.quaternion_algebra().gens()[0]
    nf = BinaryQF([1, 0, ZZ(-ii**2)])

    if not set(T.prime_factors()) <= {2}:
        raise NotImplementedError

    while True:
        e = T.valuation(2)

        if not ZZ(I.norm()).is_pseudoprime():
            raise NotImplementedError
#            I = equivalent_prime_ideal(I)

        N,α = norm_and_generator(I)

        for s1 in range(1, e+1):
            γ = represent_integer(I.left_order(), N << s1)
            if γ is not None:
                break
        else:
            assert False
        O0 = I.left_order()

        C,D = ideal_mod_constraint(N, α, γ)
        print(f'{C = }')
        print(f'{D = }')
        if N.divides(nf(C,D)):
            raise NotImplementedError('bad')

        µ = strong_approximation(N, α, C, D, ZZ(1) << (e-s1))

        return γ * µ

