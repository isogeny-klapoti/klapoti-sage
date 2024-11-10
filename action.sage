#!/usr/bin/env sage
proof.all(False)

from myklpt import klpt

from theta_structures.couple_point import CouplePoint
from theta_isogenies.product_isogeny import EllipticProductIsogeny

sys.setrecursionlimit(9999)

class KLaPoTi_Context:

    def __init__(self, ω, β):
        self.ω = ω
        self.β = β
        self.e1 = ZZ(log(ω.norm() + β.norm(), 2))

        self.O = self.ω.parent().order(ω)

    def secret(self):
        G = BQFClassGroup(self.O.discriminant())
        Q = G.random_element()
        I = self.O.ideal(Q.form())
        F,(N,α) = I.quadratic_form(basis=True)
        bnd = 1
        while True:
            for _ in range(99):
                u = randrange(bnd+1)
                v = randrange(bnd+1)
                assert F(u,v) == (u*N + v*α).norm() / N
                newN = F(u,v)
                assert newN.parent() is ZZ
                if newN.is_pseudoprime() and not Mod(2,newN).is_square():
                    break
            else:
                bnd += 1
                continue
            break
        δ = u*N + v*α
        J = self.O.ideal([(g * δ.conjugate() / N) for g in I.gens()])
        assert J.is_equivalent(I)
        return J


load('canonical.sage')


t_normequation = []
t_computeisogeny = []
t_pushorientation = []
t_canonicalrepr = []

class KLaPoTi_PublicKey:

    def __init__(self, ctx, E, P, Q, ωP, ωQ, *, canonicalize=True, Hcnt_post=None):
        self.ctx = ctx

        self.p = E.base_field().characteristic()
        self.e2 = (self.p + 1).valuation(2) - 1 - vector(list(self.ctx.ω) + list(self.ctx.β)).denominator().valuation(2)

        import time; t0 = time.time()

        assert is_montgomery(E)

        if canonicalize:
            P.set_order(2^(self.e2+2), check=False)
            Q.set_order(2^(self.e2+2), check=False)
            E, P, Q, ωP, ωQ = canonicalize_orientation(E, P, Q, ωP, ωQ)

            t_canonicalrepr.append(time.time() - t0); t0 = time.time()

        self.E = E
        self.P, self.Q, self.ωP, self.ωQ = P, Q, ωP, ωQ

        E.set_order((self.p+1)^2, check=False)
        for pt in (self.P, self.Q, self.ωP, self.ωQ):
            pt.set_order(2^(self.e2+2), check=False)

    def __repr__(self):
        A = self.E.a2()
        assert self.E == EllipticCurve([0,A,0,1,0])
        return f'KLaPoTi<{A}, {self.ωP.xy()}, {self.ωQ.xy()}>'

    def act(self, aa):
        from sage.groups.generic import order_from_multiple

        import time; t0 = time.time()

        N, α = aa.gens_two()
        N = ZZ(N)
        print(f'{N = }')
        print(f'{α = }')
        print(f'{N.factor() = }')

        ϑ = α.parent().number_field().gen()

        Quat.<i,j,k> = QuaternionAlgebra(-1, α.parent().discriminant())
        assert (α[0] + α[1]*j).reduced_norm() == α.norm()
        assert (α[0] + α[1]*j).reduced_trace() == α.trace()
        assert j.reduced_norm() == ϑ.norm() and j.reduced_trace() == ϑ.trace()
        assert (ϑ+1)/2 in self.ctx.O
        OO = Quat.quaternion_order([1, i, (1+j)/2, (i+k)/2])
        I = OO*N + OO*(α[0] + α[1]*j)
        print(f'{I = }')

        #XXX
        elt = klpt(I, 2^self.e2)
        assert elt in I
        assert ZZ(elt.reduced_norm()).divides(ZZ(I.norm()) << self.e2)
        print(f'{elt = }', '| norm:', elt.reduced_norm().factor())
        #XXX

        b = elt[0] + elt[2]*ϑ
        c = elt[1] + elt[3]*ϑ
        while b and c and b/2 in aa and c/2 in aa:  #XXX can we avoid this a priori in KLPT?
            b /= 2
            c /= 2
        print(f'{b = }')
        print(f'{c = }')
        assert b in aa
        assert c in aa
        O = aa.ring()
        bb = O.ideal([g*b.conjugate()/aa.norm() for g in aa.gens()])
        cc = O.ideal([g*c.conjugate()/aa.norm() for g in aa.gens()])
        print(f'{bb = }', bb.norm())#.factor())
        print(f'{cc = }', cc.norm())#.factor())
        assert ZZ(bb.norm() + cc.norm()).prime_divisors() == [2]
        if bb.norm().gcd(cc.norm()) != 1:
            print(f'\x1b[31mgcd is {bb.norm().gcd(cc.norm()).factor()}\x1b[0m')
            raise NotImplementedError('#sad')

        N = ZZ(bb.norm() + cc.norm())
        print(f'N = {N.factor()}')
        ee = ZZ(log(N, 2))
        assert ee <= self.e2

        γ, = (bb * cc.conjugate()).gens_reduced()
        assert γ.norm() == bb.norm() * cc.norm()
        u,v = self.ctx.ω.coordinates_in_terms_of_powers()(γ)
        assert γ == u + v*self.ctx.ω
        γP = u*self.P + v*self.ωP
        γQ = u*self.Q + v*self.ωQ
        print(f'{γ = }')

        t_normequation.append(time.time() - t0); t0 = time.time()

        Nb = ZZ(bb.norm())
        cof = 2^(self.e2 - ee)
        ker = ((cof*Nb*self.P, cof*γP), (cof*Nb*self.Q, cof*γQ))

        H2 = lambda tup: (tup[0]+tup[1], tup[0]-tup[1])

        e = ee
        while not 2^(e+1) * (ker[0][0] - ker[0][1]):
            ker = tuple(map(H2, ker))
            e -= 1
#        assert all(2^(e+1)*pt and not 2^(e+2)*pt for pts in ker for pt in pts)
        Psi = EllipticProductIsogeny(tuple(CouplePoint(*pt) for pt in ker), e)
        Psi._codomain[0].set_order((self.p+1)^2)  #XXX
        Psi._codomain[1].set_order((self.p+1)^2)  #XXX
        def _pre():
            def _aux(pt):
                for _ in range(ee - e):
                    pt = H2(pt)
                return CouplePoint(*pt)
            return _aux
        pre = _pre()
        o = self.P._order
        z = self.P.weil_pairing(self.Q, o)
#        assert z.multiplicative_order() == o
        def _ev():
            #TODO these evaluations could be reused below
            for i in range(2):
                imP = Psi(pre(CouplePoint((1-i)*self.P, i*self.P)))
                imQ = Psi(pre(CouplePoint((1-i)*self.Q, i*self.Q)))
                for j in range(2):
                    imP[j].set_order(o, check=False)
                    imQ[j].set_order(o, check=False)
                    w = imP[j].weil_pairing(imQ[j], o)
                    if z^Nb in (w, ~w):
                        def _fun(pt):
                            return Psi(pre(CouplePoint((1-i)*pt, i*pt)))[j]
                        return _fun
                else:
                    assert False
            assert False
        self.ev = _ev()

        t_computeisogeny.append(time.time() - t0); t0 = time.time()

        imP = self.ev(self.P)
        imQ = self.ev(self.Q)
        if imP.weil_pairing(imQ, o) != z^Nb:
            imQ = -imQ
        assert imP.weil_pairing(imQ, o) == z^Nb

        assert self.ωP.weil_pairing(self.ωQ, o) == z^self.ctx.ω.norm()
        imωP = self.ev(self.ωP)
        imωQ = self.ev(self.ωQ)
        if imωP.weil_pairing(imωQ, o) != z^(Nb*self.ctx.ω.norm()):
            imωQ = -imωQ
        assert imωP.weil_pairing(imωQ, o) == z^(Nb*self.ctx.ω.norm())

        # This might still be -ω now; check using 1±ω
        if (imωP+imP).weil_pairing(imωQ+imQ, o) != z^(Nb*(self.ctx.ω+1).norm()):
            imωP, imωQ = -imωP, -imωQ
        assert (imωP+imP).weil_pairing(imωQ+imQ, o) == z^(Nb*(self.ctx.ω+1).norm())

        imE = imP.curve()
        imE.set_order((self.p+1)^2, check=False)
        imP.set_order(o, check=False)
        imQ.set_order(o, check=False)
        imωP.set_order(o, check=False)
        imωQ.set_order(o, check=False)

        t_pushorientation.append(time.time() - t0); t0 = time.time()

        return KLaPoTi_PublicKey(self.ctx, imE, imP, imQ, imωP, imωQ)#, Hcnt_post=self.ω.Hcnt_post)


def timers():
    print('time for solving the norm equation (KLPT):           ', sum(t_normequation))
    print('time for computing the actual isogeny (2-dim):       ', sum(t_computeisogeny))
    print('time for pushing the orientation through (2-dim):    ', sum(t_pushorientation))
    print('time for finding a canonical representation (1-dim): ', sum(t_canonicalrepr))

def reset_timers():
    global t_normequation, t_computeisogeny, t_pushorientation, t_canonicalrepr
    t_normequation, t_computeisogeny, t_pushorientation, t_canonicalrepr = [], [], [], []

################################################################

discbits = ZZ(sys.argv[1])

import ast

with open(f'data/params-{discbits}.txt') as ls:
    _d = ZZ(next(ls).removeprefix('d '))
    _f = ZZ(next(ls).removeprefix('f '))
    _K.<ϑ> = QuadraticField(_d*_f^2); del ϑ

    _ω = ast.literal_eval(next(ls).removeprefix('ω ')); _ω = _K(_ω[0]) / _ω[1]
    _β = ast.literal_eval(next(ls).removeprefix('β ')); _β = _K(_β[0]) / _β[1]

    _p = ZZ(next(ls).removeprefix('p '))
    _F2.<i> = GF((_p,2), modulus=[1,0,1])
    _E = EllipticCurve(_F2, [0, ast.literal_eval(next(ls).removeprefix('E ')), 0, 1, 0])
    _P = _E(Sequence(ast.literal_eval(next(ls).removeprefix('P ')), _F2))
    _Q = _E(Sequence(ast.literal_eval(next(ls).removeprefix('Q ')), _F2))
    _ωP = _E(Sequence(ast.literal_eval(next(ls).removeprefix('ωP ')), _F2))
    _ωQ = _E(Sequence(ast.literal_eval(next(ls).removeprefix('ωQ ')), _F2))

ctx = KLaPoTi_Context(_ω, _β)
pk0 = KLaPoTi_PublicKey(ctx, _E, _P, _Q, _ωP, _ωQ)

reset_timers()

################################################################

print(f'{pk0 = }')

sk1 = ctx.secret()
sk2 = ctx.secret()
print(sk1)
print(sk2)
pk1 = pk0.act(sk1)
print(f'\x1b[32m{pk1 = }\x1b[0m')
pk2 = pk0.act(sk2)
print(f'\x1b[32m{pk2 = }\x1b[0m')

ss1 = pk2.act(sk1)
print(f'\x1b[32m{ss1 = }\x1b[0m')
ss2 = pk1.act(sk2)
print(f'\x1b[32m{ss2 = }\x1b[0m')

print()
timers()
