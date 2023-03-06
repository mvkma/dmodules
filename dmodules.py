# TODO:
# - characteristic_ideal(I) fails if the ring of I is not of characteristic zero.
#   This can be fixed by looking at the singular code.
# - Fail for one-variable Weyl algebras
# - Use exceptions instead of assert

from collections import defaultdict

import ore_algebra

from sage.combinat.integer_vector import IntegerVectors
from sage.interfaces.singular import Singular
from sage.functions.other import factorial
from sage.misc.functional import log
from sage.misc.misc_c import prod
from sage.modules.free_module_element import vector
from sage.rings.fraction_field import FractionField_generic
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

def initial_form(op, u, v):
    """
    Initial form

    EXAMPLES::

        # From singular's dmodapp.lib
        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: F = 3*x**2*Dy+2*y*Dx; G = 2*x*Dx+3*y*Dy+6;
        sage: initial_form(F, (-1, -1), (1, 1))
        2*y*Dx
        sage: initial_form(G, (-1, -1), (1, 1))
        2*x*Dx + 3*y*Dy + 6
        sage: initial_form(F, (-1, -2), (1, 2))
        3*x^2*Dy
        sage: initial_form(G, (-1, -2), (1, 2))
        2*x*Dx + 3*y*Dy + 6
        sage: initial_form(F, (-2, -3), (2, 3))
        2*y*Dx + 3*x^2*Dy 
        sage: initial_form(G, (-2, -3), (2, 3))
        2*x*Dx + 3*y*Dy + 6

        sage: H = (10*x**2 - x*y - 1/3*y**2 - 1/3*x - 1/10)*Dx**2 + (2/9*x**2 + 1/2*x*y + y**2)*Dx*Dy + (-6*x*y - y**2 + 1)*Dy**2 + (5/4*x*y + 8*y**2 - 2*y)*Dy + 33*x**2 + x - y + 1 
        sage: initial_form(H, (0, 0), (1, 1))
        10*x^2*Dx^2 - x*y*Dx^2 - 1/3*y^2*Dx^2 + 2/9*x^2*Dx*Dy + 1/2*x*y*Dx*Dy + y^2*Dx*Dy - 6*x*y*Dy^2 - y^2*Dy^2 - 1/3*x*Dx^2 - 1/10*Dx^2 + Dy^2
        sage: initial_form(H, (-1, -1), (1, 1))
        (-1/10)*Dx^2 + Dy^2
        sage: initial_form(H, (-1, -2), (1, 2))
        Dy^2
        sage: initial_form(H, (-2, -3), (2, 3))
        Dy^2
    
    """
    assert isinstance(op, ore_algebra.ore_operator.OreOperator)

    # Put everything into a flat ring
    W = op.parent()
    op = op.polynomial()
    R = op.parent()
    phi = R.flattening_morphism()
    op = phi(op)

    n = int(phi.codomain().ngens() / 2)
    u = vector(u)
    v = vector(v)

    assert len(u) == len(v) == n

    supp = [m.degrees() for m in op.monomials()]
    supp = [(v[:n], v[n:]) for v in supp]

    mmap = defaultdict(list)
    mmax = None
    for a, b in supp:
        m = vector(a) * u + vector(b) * v
        mmap[m].append((a, b))
        if m is None or m > mmax:
            mmax = m

    in_form = sum(op[m[0] + m[1]] * phi.codomain().monomial(*m[0], *m[1]) for m in mmap[mmax])

    # Put the initial form in the correct space
    if all(u[i] + v[i] > 0 for i in range(n)):
        in_form = in_form
    elif all(u[i] + v[i] == 0 for i in range(n)):
        in_form = W(in_form)
    else:
        raise NotImplementedError("Mixed u + v not implemented")

    return in_form

def initial_ideal(I, u, v, final_gb=True):
    """
    Initial ideal

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: I = W.ideal([3*x**2*Dy+2*y*Dx,2*x*Dx+3*y*Dy+6])
        sage: initial_ideal(I, (-2, -3), (2, 3))
        Left Ideal ((2*x)*Dx + (3*y)*Dy + 6, (2*y)*Dx + (3*x^2)*Dy, (-4*y)*Dx^2 + (9*x*y)*Dy^2 + (15*x)*Dy, (8*y)*Dx^3 + (27*y^2)*Dy^3 + (135*y)*Dy^2 + 105*Dy) of Multivariate Ore algebra in Dx, Dy over Fraction Field of Multivariate Polynomial Ring in x, y over Rational Field

        sage: initial_ideal(I, (-1, -1), (1, 1))
        Left Ideal (y*Dx, (2*x)*Dx + (3*y)*Dy + 6, (y^2)*Dy + (2*y)) of Multivariate Ore algebra in Dx, Dy over Fraction Field of Multivariate Polynomial Ring in x, y over Rational Field

        sage: initial_ideal(I, (-1, -1), (1, 1), final_gb=False)
        Left Ideal ((2*x)*Dx + (3*y)*Dy + 6, (2*y)*Dx, (y^2)*Dy + (2*y)) of Multivariate Ore algebra in Dx, Dy over Fraction Field of Multivariate Polynomial Ring in x, y over Rational Field

        sage: H1 = x * Dy**2 + y**2 * Dx + x * y - 1
        sage: H2 = x**2 * Dx - 2 * y * Dy - 3 * x + 5
        sage: I = W.ideal((H1, H2))
        sage: initial_ideal(I, (-1, -1), (1, 1))
        Left Ideal (1) of Multivariate Ore algebra in Dx, Dy over Fraction Field of Multivariate Polynomial Ring in x, y over Rational Field

    """
    assert isinstance(I.ring(), ore_algebra.ore_algebra.OreAlgebra_generic)

    W = I.ring()
    R = W.associated_commutative_algebra()

    if isinstance(R.base_ring(), FractionField_generic):
        R = R.change_ring(R.base_ring().ring())
        W = W.change_ring(R.base_ring())
    
    phi = R.flattening_morphism()
    R = phi.codomain()

    # FIXME: This is terrible
    S = Singular()
    S.LIB("dmodapp.lib")
    sing_r = S.ring(R.characteristic(), "(" + ",".join(R.variable_names()) + ")", "dp")
    sing_w = S.Weyl()
    S.setring(sing_w)
    sing_id = S.ideal([str(g) for g in I.gens()])
    sing_id_gb = S.GBWeight(sing_id, S.intvec(*u), S.intvec(*v))

    I_gb = sing_id_gb.sage()

    if all(u[i] + v[i] > 0 for i in range(W.ngens())):
        gr = R
    elif all(u[i] + v[i] == 0 for i in range(W.ngens())):
        gr = W
    else:
        raise NotImplementedError("Mixed u + v not implemented")
        
    I_in = gr.ideal([initial_form(W(g), u, v) for g in I_gb.gens()])

    if final_gb:
        if all(u[i] + v[i] > 0 for i in range(W.ngens())):
            # commutative case
            S.setring(sing_r)
        sing_id_in = S.ideal([str(g) for g in I_in.gens()])
        sing_id_in_gb = S.slimgb(sing_id_in)
        I_in = gr.ideal(sing_id_in_gb.sage().gens())

    return I_in

def characteristic_ideal(I):
    """
    Characteristic ideal

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: I = W.ideal((2*x*Dx+3*y*Dy+6, 3*x**2*Dy+2*y*Dx, 9*x*y*Dy**2-4*y*Dx**2+15*x*Dy, 27*y**2*Dy**3+8*y*Dx**3+135*y*Dy**2+105*Dy))
        sage: characteristic_ideal(I)
        Ideal (2*x*Dx + 3*y*Dy, 3*x^2*Dy + 2*y*Dx, 9*x*y*Dy^2 - 4*y*Dx^2, 27*y^2*Dy^3 + 8*y*Dx^3) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

        sage: I = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: characteristic_ideal(I)
        Ideal (x*Dx - y*Dy, y^2*Dy^2) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

        sage: I = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: characteristic_ideal(I)
        Ideal (y^2*Dy^2, x*y*Dx*Dy, x^2*Dx^2) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

    """
    n = I.ring().ngens()
    u = (0,) * n
    v = (1,) * n

    return initial_ideal(I, u, v)

def singular_locus(I):
    """
    Singular locus

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: I = W.ideal((2*x*Dx+3*y*Dy+6, 3*x**2*Dy+2*y*Dx, 9*x*y*Dy**2-4*y*Dx**2+15*x*Dy, 27*y**2*Dy**3+8*y*Dx**3+135*y*Dy**2+105*Dy))
        sage: singular_locus(I)
        Ideal (x^3 - y^2) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

        sage: I = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: singular_locus(I)
        Ideal (x*y) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

        sage: I = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: singular_locus(I)
        Ideal (x*y) of Multivariate Polynomial Ring in x, y, Dx, Dy over Rational Field

        sage: P1 = (x * Dx)**2 - x * (x * Dx + y * Dy + 2) * (x * Dx + 3)
        sage: P2 = (y * Dy)**2 - y * (x * Dx + y * Dy + 2) * (y * Dy + 5)
        sage: I = W.ideal((P1, P2))
        sage: singI = singular_locus(I)
        sage: singI.ngens()
        1
        sage: singI.gen(0).factor()
        y * (y - 1) * x * (x - 1) * (x + y - 1)

    """
    n = I.ring().ngens()

    ch_id = characteristic_ideal(I)

    r_comm = ch_id.ring()
    diff_vars = [r_comm.gen(n+i) for i in range(n)]
    sing_id = ch_id.saturation(r_comm.ideal(diff_vars))
    sing_id = sing_id[0].elimination_ideal(diff_vars)

    return sing_id.radical()

def holonomic_rank(I):
    """
    Holonomic rank

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: I = W.ideal((2*x*Dx+3*y*Dy+6, 3*x**2*Dy+2*y*Dx, 9*x*y*Dy**2-4*y*Dx**2+15*x*Dy, 27*y**2*Dy**3+8*y*Dx**3+135*y*Dy**2+105*Dy))
        sage: holonomic_rank(I)
        1

        sage: I1 = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: holonomic_rank(I1)
        2

        sage: I0 = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: holonomic_rank(I0)
        3

        sage: P1 = (x * Dx)**2 - x * (x * Dx + y * Dy + 2) * (x * Dx + 3)
        sage: P2 = (y * Dy)**2 - y * (x * Dx + y * Dy + 2) * (y * Dy + 5)
        sage: I = W.ideal((P1, P2))
        sage: holonomic_rank(I)
        4

    """
    W = I.ring()
    R = W.associated_commutative_algebra()

    assert isinstance(R.base_ring(), FractionField_generic)

    ch_id = characteristic_ideal(I)

    return (R * ch_id).vector_space_dimension()

def apb_factors(el):
    """
    Decompose el into x^a * p(theta) * Dx^b

    See apbFactor in canonicalSeries.m2 in Macaulay2.

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)

        sage: el = (-x*y**2)*Dx*Dy + (-y**3 + y**2)*Dy**2 + (-5*x*y)*Dx + (-8*y**2 + y)*Dy + (-10*y)
        sage: facs = apb_factors(el)
        sage: facs.keys()
        dict_keys([((0, 1), (0, 0)), ((0, 0), (0, 0))])
        sage: facs[((0, 1), (0, 0))]
        [((1, 1), -1), ((0, 2), -1), ((1, 0), -5), ((0, 1), -8), ((0, 0), -10)]
        sage: facs[((0, 0), (0, 0))]
        [((0, 2), 1), ((0, 1), 1)]

        sage: el = (-x**3 + x**2)*Dx**2 + (-x**2*y)*Dx*Dy + (-6*x**2 + x)*Dx + (-3*x*y)*Dy + (-6*x)
        sage: facs = apb_factors(el)
        sage: facs.keys()
        dict_keys([((1, 0), (0, 0)), ((0, 0), (0, 0))])
        sage: facs[((1, 0), (0, 0))]
        [((2, 0), -1), ((1, 1), -1), ((1, 0), -6), ((0, 1), -3), ((0, 0), -6)]
        sage: facs[((0, 0), (0, 0))]
        [((2, 0), 1), ((1, 0), 1)]

        sage: el = x**2 * Dx**2 + x * Dx
        sage: facs = apb_factors(el)
        sage: facs.keys()
        dict_keys([((0, 0), (0, 0))])
        sage: facs[((0, 0), (0, 0))]
        [((2, 0), 1), ((1, 0), 1)]

        sage: el = x * y * Dx * Dy
        sage: facs = apb_factors(el)
        sage: facs.keys()
        dict_keys([((0, 0), (0, 0))])
        sage: facs[((0, 0), (0, 0))]
        [((1, 1), 1)]

        sage: el = x * y * Dx * Dy + x * Dx + y * Dy
        sage: facs = apb_factors(el)
        sage: facs.keys()
        dict_keys([((0, 0), (0, 0))])
        sage: facs[((0, 0), (0, 0))]
        [((1, 1), 1), ((1, 0), 1), ((0, 1), 1)]

    """
    W = el.parent()
    R = W.associated_commutative_algebra()

    if isinstance(R.base_ring(), FractionField_generic):
        R = R.change_ring(R.base_ring().ring())
        W = W.change_ring(R.base_ring())

    # el lives in K[x_1,...x_n][Dx_1,...,Dx_n]
    el = R(el.polynomial())

    terms = defaultdict(list)

    # u is the exponent vector of the Dx_i variables
    for u in el.exponents():
        u = ensure_iterable(u)
        coeff_u = el.monomial_coefficient(R.monomial(*u))

        # v is the exponent vector of the x_i variables
        for v in coeff_u.exponents():
            v = ensure_iterable(v)
            # How many times can be pair up x_i and Dx_i?
            theta_exp = [min(ui, vi) for ui, vi in zip(u, v)]
            a = tuple([vi - ti for vi, ti in zip(v, theta_exp)]) # x variables
            b = tuple([ui - ti for ui, ti in zip(u, theta_exp)]) # Dx variables

            # The exponent vector of x^w * Dx^w inside p(theta) and the corresponding coefficient
            w = tuple([i - j for i, j in zip(v, a)])
            c_w = coeff_u.monomial_coefficient(R.base_ring().monomial(*v))
            terms[(a, b)].append((w, c_w))

    return dict(terms)

def is_torus_invariant(I):
    """
    An ideal is torus invariant if it generated by elements of the form x^a * p(theta) * Dx^b

    EXAMPLES::
    
        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: I = W.ideal((2*x*Dx+3*y*Dy+6, 3*x**2*Dy+2*y*Dx, 9*x*y*Dy**2-4*y*Dx**2+15*x*Dy, 27*y**2*Dy**3+8*y*Dx**3+135*y*Dy**2+105*Dy))
        sage: is_torus_invariant(I)
        False

        sage: I1 = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: is_torus_invariant(I1)
        True

        sage: I0 = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: is_torus_invariant(I0)
        True

        sage: P1 = (x * Dx)**2 - x * (x * Dx + y * Dy + 2) * (x * Dx + 3)
        sage: P2 = (y * Dy)**2 - y * (x * Dx + y * Dy + 2) * (y * Dy + 5)
        sage: I = W.ideal((P1, P2))
        sage: is_torus_invariant(I)
        False

    """
    W = I.ring()
    R = W.associated_commutative_algebra()

    if isinstance(R.base_ring(), FractionField_generic):
        R = R.change_ring(R.base_ring().ring())
        W = W.change_ring(R.base_ring())

    new_gens = []
    for g in I.gens():
        facs = apb_factors(g)

        for ab, terms in facs.items():
            a, b = ab
            xa = R.base_ring().monomial(*a)
            dxb = prod(W.gen(i)**b[i] for i in range(W.ngens()))
            p = W(0)
            for t in terms:
                mon = prod(R.base_ring().gen(i)**t[0][i] * W.gen(i)**t[0][i] for i in range(W.ngens()))
                p += t[1] * mon

            new_g = xa * p * dxb
            new_gens.append(new_g)
            g -= new_g

        # Check that no factors got lost
        assert g == 0

    return I == W.ideal(new_gens)

def distraction(I, theta_ring):
    """
    Distraction

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: S.<t1,t2> = PolynomialRing(QQ)

        sage: I1 = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: distraction(I1, S)
        Ideal (t1^2 + t1, t1*t2 + t1, t1*t2 + t2, t2^2 + t2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

        sage: I0 = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: distraction(I0, S)
        Ideal (t1^2, t1*t2, t2^2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

    """
    W = I.ring()

    assert W.ngens() == theta_ring.ngens()

    if not is_torus_invariant(I):
        raise ValueError("Ideal I is not torus invariant")

    new_gens = []
    for g in I.gens():
        facs = apb_factors(g)

        new_g = theta_ring(0)
        for ab, terms in facs.items():
            _, b = ab
            p = theta_ring(0)
            for t in terms:
                mon = prod(prod(theta_ring.gen(k) - i for i in range(t[0][k])) for k in range(W.ngens()))
                p += t[1] * mon

            p_b = p.subs({theta_ring.gen(i): theta_ring.gen(i) - b[i] for i in range(W.ngens())})
            br = prod(prod(theta_ring.gen(i) - j for j in range(b[i])) for i in range(W.ngens()))

            new_g += br * p_b

        new_gens.append(new_g)

    return theta_ring.ideal(new_gens)

def indicial_ideal(I, w, theta_ring):
    """
    Indicial ideal with respect to weight vector w

    EXAMPLES::

        sage: import ore_algebra
        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: S.<t1,t2> = PolynomialRing(QQ)

        sage: I = W.ideal((2*x*Dx+3*y*Dy+6, 3*x**2*Dy+2*y*Dx, 9*x*y*Dy**2-4*y*Dx**2+15*x*Dy, 27*y**2*Dy**3+8*y*Dx**3+135*y*Dy**2+105*Dy))
        sage: indicial_ideal(I, (1, 1), S)
        Ideal (t1, 2*t1 + 3*t2 + 6, t2 + 2) of Multivariate Polynomial Ring in t1, t2 over Rational Field
        sage: indicial_ideal(I, (1, 3), S)
        Ideal (2*t1 + 3*t2 + 6, t2, 3*t2^2 + 2*t2, 9*t2^3 + 18*t2^2 + 8*t2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

        sage: I1 = W.ideal((x * Dx * (x * Dx + 1), x * Dx * (y * Dy + 1), y * Dy * (x * Dx + 1), y * Dy * (y * Dy + 1)))
        sage: indicial_ideal(I1, (1, 1), S)
        Ideal (t1 - t2, t2^2 + t2) of Multivariate Polynomial Ring in t1, t2 over Rational Field
        sage: indicial_ideal(I1, (2, 3), S)
        Ideal (t1 - t2, t2^2 + t2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

        sage: I0 = W.ideal((x * Dx * x * Dx, x * Dx * y * Dy, y * Dy * y * Dy))
        sage: indicial_ideal(I0, (1, 1), S)
        Ideal (t2^2, t1*t2, t1^2) of Multivariate Polynomial Ring in t1, t2 over Rational Field
        sage: indicial_ideal(I0, (2, 3), S)
        Ideal (t2^2, t1*t2, t1^2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

        sage: P1 = (x * Dx)**2 - x * (x * Dx + y * Dy + 2) * (x * Dx + 3)
        sage: P2 = (y * Dy)**2 - y * (x * Dx + y * Dy + 2) * (y * Dy + 5)
        sage: I = W.ideal((P1, P2))
        sage: indicial_ideal(I, (1, 1), S)
        Ideal (t2^2, t1^2) of Multivariate Polynomial Ring in t1, t2 over Rational Field
        sage: indicial_ideal(I, (2, 3), S)
        Ideal (t2^2, t1^2) of Multivariate Polynomial Ring in t1, t2 over Rational Field

    """
    u = tuple(-i for i in w)
    v = w
    return distraction(initial_ideal(I, u, v), theta_ring)

def standard_monomials(I):
    """
    Standard monomials with respect to term order

    Better: use I.normal_basis

    EXAMPLES::

        sage: S.<t1,t2,t3,t4,t5> = PolynomialRing(QQ)
        sage: I = S.ideal([t3 + 2*t4 + t5, t2 - 3*t4 - t5, t1 + 2*t4 + t5, 8*t4*t5 + 3*t5^2, 8*t4^2 - t5^2, t5^3])
        sage: standard_monomials(I)
        [1, t4, t5, t5^2]

        sage: I = S.ideal([t1*t3, t1*t4, t2*t4, t2*t5, t3*t5, t1 + t2 - t4, t2 + t3 - t5])
        sage: standard_monomials(I)
        [1, t3, t4, t5, t4*t5]

        sage: R.<x,y,z> = PolynomialRing(QQ)
        sage: I = R.ideal(x**2-2*x*z+5, x*y**2+y*z+1, 3*y**2-8*x*z)
        sage: standard_monomials(I)
        [1, x, y, z, x*y, x*z, y*z, z^2]

    """
    R = I.ring()
    gb_I = I.groebner_basis()
    in_I = [max(g.monomials()) for g in gb_I]

    assert I.dimension() == 0 # otherwise this is not a finite set
    assert all(g.is_monomial() for g in in_I)

    in_I_exps = [vector(mon.exponents()[0]) for mon in in_I]

    # Brute force search for standard monomials
    degmax = max(m.degree() for m in in_I)
    standard_mons = []
    for deg in range(degmax + 1):
        for ivec in IntegerVectors(n=deg, k=R.ngens()):
            for mon_exp in in_I_exps:
                if not any(ivec[i] < mon_exp[i] for i in range(R.ngens())):
                    break
            else:
                standard_mons.append(R.monomial(*ivec))

    return standard_mons

def classical_sols_frobenius(I):
    """
    Classical solutions for Frobenius ideal (algorithm 2.3.14)

    EXAMPLES::

        sage: S.<t1,t2,t3,t4,t5> = PolynomialRing(QQ)
        sage: I = S.ideal([t3 + 2*t4 + t5, t2 - 3*t4 - t5, t1 + 2*t4 + t5, 8*t4*t5 + 3*t5**2, 8*t4**2 - t5**2, t5**3])
        sage: sols = classical_sols_frobenius(I)
        sage: [c.factor() for c in sols]
        [1,
         (-1) * (2*t1 - 3*t2 + 2*t3 - t4),
         (-1) * (t1 - t2 + t3 - t5),
         (1/8) * (t2 + t4 - 2*t5) * (2*t1 - t2 + 2*t3 + t4 - 4*t5)]

        sage: S.<t1,t2> = PolynomialRing(QQ)
        sage: I = S.ideal((t1**2, t1 * t2, t2**2))
        sage: sols = classical_sols_frobenius(I)
        sage: [c.factor() for c in sols]
        [1, t1, t2]

        sage: I = S.ideal((t1, t2))
        sage: sols = classical_sols_frobenius(I)
        sage: [c.factor() for c in sols]
        [1]

    """
    # TODO: There should be some checks here
    R = I.ring()
    gb_I = I.groebner_basis()
    in_I = [max(g.monomials()) for g in gb_I]

    assert all(g.is_monomial() for g in in_I)

    standard_mons = standard_monomials(I)

    degmax = max(m.degree() for m in in_I)
    coeffs = defaultdict(R)
    for deg in range(degmax + 1):
        for ivec in IntegerVectors(n=deg, k=R.ngens()):
            mon = R.monomial(*ivec)
            rem = mon.reduce(gb_I)
            for m, c in zip(rem.monomials(), rem.coefficients()):
                assert m in standard_mons
                fac = R(prod(map(factorial, m.exponents()[0]))) / R(prod(map(factorial, mon.exponents()[0])))
                coeffs[m] += c * mon * fac

    return list(coeffs.values())

def classical_solutions(I, w, starting_monomials=False):
    """
    Classical solutions with respect to weight vector w

    EXAMPLES::

        sage: R = PolynomialRing(QQ, names=["x1", "x2", "x3", "x4", "x5"])
        sage: W = ore_algebra.OreAlgebra(R, names=["Dx1", "Dx2", "Dx3", "Dx4", "Dx5"])
        sage: th = lambda i: R.gen(i-1) * W.gen(i-1)
        sage: I = W.ideal([th(1) + th(2) + th(3) + th(4) + th(5), th(1) + th(2) - th(4), th(2) + th(3) - th(4), th(1) * th(3), th(2) * th(4)])
        sage: solsI = classical_solutions(I, (1, 1, 1, 1, 1))
        sage: solsI
        [1,
         -2*log(x1) + 3*log(x2) - 2*log(x3) + log(x4),
         -log(x1) + log(x2) - log(x3) + log(x5),
         1/4*log(x1)*log(x2) - 1/8*log(x2)^2 + 1/4*log(x2)*log(x3) + 1/4*log(x1)*log(x4) + 1/4*log(x3)*log(x4) + 1/8*log(x4)^2 - 1/2*log(x1)*log(x5) - 1/4*log(x2)*log(x5) - 1/2*log(x3)*log(x5) - 3/4*log(x4)*log(x5) + log(x5)^2]
        sage: [[SR(dop(sol)).canonicalize_radical() for dop in I.gens()] for sol in solsI]
        [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]

        sage: R.<x,y> = PolynomialRing(QQ)
        sage: W.<Dx,Dy> = ore_algebra.OreAlgebra(R)
        sage: P1 = (x * Dx)**2 - x * (x * Dx + y * Dy + 2) * (x * Dx + 3)
        sage: P2 = (y * Dy)**2 - y * (x * Dx + y * Dy + 2) * (y * Dy + 5)
        sage: I = W.ideal((P1, P2))
        sage: solsI = classical_solutions(I, (1, 1))
        sage: solsI
        [1, log(x), log(y), log(x)*log(y)]

        sage: Rxy.<x,y> = PolynomialRing(QQ)
        sage: Wxy.<Dx,Dy> = ore_algebra.OreAlgebra(Rxy)
        sage: Sxy.<s1,s2> = PolynomialRing(QQ)
        sage: P1 = (x*Dx)**2 * (x*Dx - 2) - x * (x*Dx + y*Dy + 8) * (x*Dx + 11) * (x*Dx + 15)
        sage: P2 = (y*Dy)**2 * (y*Dy - 3) - y * (x*Dx + y*Dy + 8) * (y*Dy + 13) * (y*Dy + 19)
        sage: Ixy = Wxy.ideal((P1, P2))
        sage: classical_solutions(Ixy, (1, 1), starting_monomials=True)
        [x^2, x^2*log(y), x^2*y^3, 1, log(x), log(y), log(x)*log(y), y^3, y^3*log(x)]

    """
    W = I.ring()
    R = W.base_ring()

    S = PolynomialRing(R.base_ring(), [f"th{i}" for i in range(W.ngens())])
    ind = indicial_ideal(I, w, S)

    ind_dec = ind.primary_decomposition()

    to_logs = {S.gen(i): log(R.gen(i)) for i in range(R.ngens())}
    sols = []
    for Q in ind_dec:
        pts = Q.variety()
        assert len(pts) == 1

        mul = Q.vector_space_dimension()
        sols_frobenius = classical_sols_frobenius(Q)
        assert mul == len(sols_frobenius)

        # Return only starting monomials, i.e. extract the lowest monomials from the solutions
        if starting_monomials:
            sols_frobenius = [min(sol.monomials()) for sol in sols_frobenius]

        pre = prod(R.gen(i)**(S.gen(i).subs(pts[0])) for i in range(W.ngens()))
        sols_log = []
        for s in sols_frobenius:
            sols_log.append(pre * s.subs(to_logs))

        sols += sols_log

    return sols

def ensure_iterable(el):
    """
    Ensure that el is iterable
    """
    if not hasattr(el, "__iter__"):
        return (el,)
    else:
        return el
