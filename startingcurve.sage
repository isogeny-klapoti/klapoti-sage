#!/usr/bin/env sage
proof.all(False)

bits = ZZ(sys.argv[1])
outf = open(f'data/params-{bits}.txt', 'w')

d = -11

f = ceil(sqrt(abs((2^bits)/d)))
while f > 1:
    f -= 1
    if f % 4 != 3:
        continue
    if f.is_prime():
        break
else:
    assert False

disc = d * f^2
K.<ϑ> = QuadraticField(disc)
O = K.order_of_conductor(f)
assert O.discriminant() == disc

print(f'd {d}', file=outf)
print(f'f {f}', file=outf)
print(f'disc = {d} * {f}^2')
print(f'log2|disc| = {abs(disc).log(2).n()}')

################################################################

C = 99  #TODO

emax = ceil((C * log(disc.abs(),2) * disc.abs()).log(2)) - 2

assert disc < 0
assert disc % 8 == 5

for e in range(ceil(RealField(9999)(log(-disc,2))), emax+1):
    for z in range(ceil(sqrt(-2^(e+2)/disc - 1))):
        M = 2^(e+2) + disc*(z^2+1)
        assert M >= 0
        if (M.is_prime() and M%4==1) or (M/2 in ZZ and ZZ(M/2).is_prime() and (M/2)%4==1):
            X,Y = two_squares(M)
            if X % 2 == 0:
                X,Y = Y,X
            if X % 2 == 0:
                continue
            x = (X-disc)/2
            y = (Y-z*disc)/2
            if x and y:
                break
    else:
        continue
    break
else:
    raise NotImplementedError

################################################################

assert ϑ^2 == disc
gen = (disc + ϑ) / 2
assert gen in O
ω = x + gen
β = y + z*gen

assert ω in O and β in O
assert ω.minpoly().discriminant() == disc
assert gcd(ω.norm(), β.norm()) == 1
assert ω.norm() + β.norm() == 2^e

print(f'{e = }', file=sys.stderr)
print(list(ω))
print(list(β))

print(f'ω {list(ω*ω.denominator())}, {ω.denominator()}', file=outf)
print(f'β {list(β*β.denominator())}, {β.denominator()}', file=outf)

################################################################

klpt_exponent = 3.4  #TODO

emax = ceil(klpt_exponent * log(abs(disc),2).n() / 64) * 64 - 1
emin = emax - 4*bits.bit_length()
assert emin >= e
maxcof = 1024
ps = set()
for cur_e in range(emin, emax):
    p = -1
    for _ in range(1,maxcof):
        p += 2**cur_e
        if (p+1).valuation(2) > cur_e:
            continue
        if p % 4 != 3:
            continue
        if not Mod(-p, f).is_square():
            continue
        if not p.is_prime():
            continue
        if K.ideal(p).is_prime():  # inert -> supersingular
            ps.add(p)
assert ps
ps = sorted(ps, key = lambda p: (p+1).prime_to_m_part(2))
#for p in ps:
#    print(p.log(2).n(), factor(p+1))
p = ps[0]

print(f'log2(p) = {p.log(2).n()}')
print(f'{p = }')
print(f'p+1 = {(p+1).factor()}')

print(f'p {p}', file=outf)

################################################################

def torsion(E, d):
    F = E.base_field()
    deg = next(k for k in range(1,d+1) if d.divides(E.order(extension_degree=k).sqrt()))
    Fext = F.extension(deg, 'a') if deg > 1 else F
    Eext = E.change_ring(Fext)
    assert d.divides(Eext.order().sqrt())
    rem = Eext.order() // Eext.order().prime_to_m_part(d)
    from sage.groups.generic import has_order
    while True:
        P = Eext.random_point()
        P *= Eext.order().prime_to_m_part(d)
        P.set_order(multiple=rem)
        if d.divides(P.order()):
            P *= P.order() // d
            P.set_order(d)
            break
    while True:
        Q = Eext.random_point()
        Q *= Eext.order().prime_to_m_part(d)
        Q.set_order(multiple=rem)
        if d.divides(Q.order()):
            Q *= Q.order() // d
            Q.set_order(d)
            if has_order(P.weil_pairing(Q, d), d, '*'):
                break
    return P, Q

################################################################

q = abs(d); assert q.is_prime()

F2.<i> = GF((p,2), modulus=[1,0,1])

j0, = hilbert_class_polynomial(d).roots(ring=GF(p), multiplicities=False)
E0 = EllipticCurve(j=F2(j0))
E0.set_order((p+1)^2)
frob = E0.frobenius_isogeny(); assert frob.is_endomorphism()
ιmap = next(iso*psi for psi in E0.isogenies_prime_degree(q)
                    for iso in psi.codomain().isomorphisms(E0)
                    if (iso*psi).scaling_factor().trace() == 0)
R = E0.random_point(); assert (ιmap^2)(R) == -q*R  # check


Quat.<ii,jj,kk> = QuaternionAlgebra(-q, -p)
assert Quat.discriminant() == p

surface = len(E0.change_ring(GF(p)).abelian_group().invariants()) == 2
c = min(map(ZZ, Mod(-p,q).sqrt(all=True)))
P,Q = torsion(E0,q)
if surface:
    raise NotImplementedError
elif not any(c*ιmap._eval(T) + ιmap._eval(frob._eval(T)) for T in (P,Q)):
    O0 = Quat.quaternion_order([Quat.one(), (1+ii)/2, (jj+kk)/2, (c*ii+kk)/q])
else:
    assert not any(c*ιmap._eval(T) - ιmap._eval(frob._eval(T)) for T in (P,Q))
    O0 = Quat.quaternion_order([Quat.one(), (1+ii)/2, (jj+kk)/2, (c*ii-kk)/q])
assert surface == ((1+jj)/2 in O0)

# check
assert O0.discriminant() == Quat.discriminant()
if 0:   # slow
    for el in O0.basis():
        d = el.denominator()
        t,u,v,w = el * d
        P,Q = torsion(E0, d)
        for T in torsion(E0,d):
            assert not t*T + u*ιmap._eval(T) + v*frob._eval(T) + w*ιmap._eval(frob._eval(T))

################################################################

v0 = ZZ(Mod(-p, f).sqrt(extend=False))
big = 2^ceil(log(p,2) + 5)
v,w = next(filter(all, matrix([[v0, 1], [f, 0], [0, f]]).LLL()))
assert vector(GF(f), [v,w]) / vector(GF(f), [v0,1]) in GF(f)

γ0 = v + w*jj
assert γ0.reduced_norm().gcd(f^2) == f
I0 = O0*f + O0*γ0
assert I0.norm() == f
assert I0 * jj == jj * I0
assert I0 * ii != ii * I0

################################################################

assert I0.norm() % 2

import traceback
from deuring2d import Deuring2D

F4.<U> = F2.extension(2)
assert F4.coerce_map_from(F2)

for deg in range(1,8):  #XXX
    print(f'\x1b[33mtrying extension of degree 2^{deg}\x1b[0m')
    Fbig.<V> = F4.extension(2**deg)
    print(f'{Fbig = }')
    assert Fbig.coerce_map_from(F2)
    assert Fbig.coerce_map_from(F4)
    assert Fbig.coerce_map_from(F4)(F4.coerce_map_from(F2)(F2.gen())) == Fbig.coerce_map_from(F2)(F2.gen())

    ctx = Deuring2D(p)

    ###XXX massive hack
    ctx.E0 = ctx.E0.change_ring(Fbig)
    print(f'e = {ctx.E0.order().sqrt().valuation(2)}')
    ctx.e = ctx.E0.order().sqrt().valuation(2) - 1
    ctx.P, ctx.Q = torsion(ctx.E0, 2**ctx.e)
    ###XXX end of hack

    realO0 = ctx.O0.order
    i0,j0,k0 = realO0.quaternion_algebra().gens()
    imii = i0 * sum(c*g for c,g in zip(QuadraticForm(QQ, 2, [1,0,p]).solve(q), (1,j0)))
    imkk = k0 * sum(c*g for c,g in zip(QuadraticForm(QQ, 2, [1,0,p]).solve(q), (1,j0)))
    assert imii^2 == -q
    assert imii*j0 == -j0*imii
    assert imkk^2 == -p*q

    # ideal connecting O0 from Deuring2D with "our" O0
    J0 = realO0 * realO0.quaternion_algebra().quaternion_order([sum(c*g for c,g in zip(elt, (realO0.quaternion_algebra().one(),imii,j0,imkk))) for elt in O0.basis()])
    while True:
        a = sum(randrange(-2,3)*g for g in J0.reduced_basis())
        if a.reduced_norm() / J0.norm() % 2:
            break
    J0 *= a.conjugate() / J0.norm()
    assert J0.norm() % 2
    print(f'{J0 = }')
    print(f'{J0.norm() = }')

    # ideal connecting "our" O0 with the target curve
    J1 = realO0.quaternion_algebra().ideal([sum(a*c*g*~a for c,g in zip(elt, (realO0.quaternion_algebra().one(),imii,j0,imkk))) for elt in I0.basis()])
    assert J0.right_order() == J1.left_order()
    print(f'{J1 = }')
    print(f'{J1.norm() = }')

    try:
        imE0, imP0, imQ0 = ctx.IdealToIsogeny(J0)
        print(f'{imE0 = }')
        print(f'{imP0 = }')
        print(f'{imQ0 = }')
    except Deuring2D.Failure as e:
        print(f'\x1b[31m{e}\x1b[0m', file=sys.stderr, flush=True)
        continue

    iso = imE0.isomorphism_to(E0.change_ring(imE0.base_field()))
    imE0 = iso.codomain()
    imP0, imQ0 = map(iso, (imP0, imQ0))
    imP0.set_order(multiple=2^ctx.e)
    imQ0.set_order(multiple=2^ctx.e)

    try:
        imE1, imP1, imQ1 = ctx.IdealToIsogeny(J0 * J1)
        print(f'{imE1 = }')
        print(f'{imP1 = }')
        print(f'{imQ1 = }')
    except Deuring2D.Failure as e:
        print(f'\x1b[31m{e}\x1b[0m', file=sys.stderr, flush=True)
        continue

    E = imE1.change_ring(F2)
    imP1.set_order(multiple=2^ctx.e)
    imQ1.set_order(multiple=2^ctx.e)

    break

# realO0 --J0-> O0 --J1-> O1
# j=1728 --ψ0-> E0 --φ--> E
# hence φ maps (P0,Q0) to (P1,Q1)
# fι = φ o ι o φ^

################################################################

ι = K['x']([q,0,1]).any_root()
u,v = (f*ι).coordinates_in_terms_of_powers()(ω)
assert ω == u + v*f*ι
w = lcm(u.denominator(), v.denominator())
assert w in (1, 2)

tors = ZZ(p+1).p_primary_part(2)
o, = {imP0.order(), imQ0.order(), imP1.order(), imQ1.order()}
P0, Q0, P1, Q1 = (ZZ(o/(tors*w)) * T for T in (imP0, imQ0, imP1, imQ1))
for T in (P0, Q0, P1, Q1): T.set_order(multiple=tors*w)
o, = {P0.order(), Q0.order(), P1.order(), Q1.order()}
assert o == tors*w

deg = lcm(ZZ(c.minpoly().degree()) for T in (P0,Q0,P1,Q1) for c in T)

P0, Q0, P1, Q1 = (T.change_ring(F4) for T in (P0, Q0, P1, Q1))
for T in (P0, Q0, P1, Q1): T.set_order(multiple=tors*w)

G0 = AdditiveAbelianGroupWrapper(P0.parent(), [P0,Q0], [o,o])
G1 = AdditiveAbelianGroupWrapper(P1.parent(), [P1,Q1], [o,o])
matι = matrix(Zmod(o), [G0.discrete_log(ιmap._eval(pt)) for pt in (P0,Q0)])
assert matι^2 == -q
matfι = f * matι
assert matfι^2 == disc
#print('matfι:')
#print(f'{matfι}')

P = (w * P1).change_ring(F2)
Q = (w * Q1).change_ring(F2)
P.set_order(multiple=p+1)
Q.set_order(multiple=p+1)
print(list(P))
print(list(Q))
assert P.order() == tors
assert Q.order() == tors

matwω = (ZZ(u*w) + ZZ(v*w)*matfι).change_ring(ZZ)
assert matwω.change_ring(Zmod(w*tors)).charpoly() == (w*ω).charpoly().change_ring(Zmod(w*tors))

ωP = (matwω[0][0]*ZZ(o/(tors*w))*P1 + matwω[0][1]*ZZ(o/(tors*w))*Q1).change_ring(F2)
ωQ = (matwω[1][0]*ZZ(o/(tors*w))*P1 + matwω[1][1]*ZZ(o/(tors*w))*Q1).change_ring(F2)
ωP.set_order(multiple=p+1)
ωQ.set_order(multiple=p+1)
print(list(ωP))
print(list(ωQ))
assert ωP.order() == tors
assert ωQ.order() == tors

assert ωP.weil_pairing(ωQ, tors) == P.weil_pairing(Q, tors)^abs(ω.norm())

################################################################

if 0:   # _very_ slow
    for myφ_ in E0.isogenies_prime_degree(f):
        for iso in myφ_.codomain().isomorphisms(E):
            myφ = iso * myφ_
            for _ in range(5):
                rpt = E0.random_point()
                print(γmap(myφ.dual()(ψmap(rpt))) == normγ * rpt, end=' ')
            mm = matrix(Zmod(w*tors), [G1.discrete_log(myφ._eval(pt)) for pt in (P0,Q0)])
            print('??')
            print(mm)
            myfι = myφ * ιmap * myφ.dual()
            if myfι^2 == -f^2*q:
                print('yes!')
                mm = matrix(Zmod(w*tors), [G1.discrete_log(myfι._eval(pt)) for pt in (P1,Q1)])
                print(mm)
            else:
                print('no...')

################################################################

load('canonical.sage')

E, P, Q, ωP, ωQ = canonicalize_orientation(E, P, Q, ωP, ωQ)

################################################################

assert is_montgomery(E)
print('E', list(E.a2()), file=outf)
print('P', list(map(list, P.xy())), file=outf)
print('Q', list(map(list, Q.xy())), file=outf)
print('ωP', list(map(list, ωP.xy())), file=outf)
print('ωQ', list(map(list, ωQ.xy())), file=outf)

