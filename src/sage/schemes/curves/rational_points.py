r"""
Enumeration of rational points on affine schemes

Naive algorithms for enumerating rational points over `\QQ` or finite fields
over for general schemes.

.. WARNING::

    Incorrect results and infinite loops may occur if using a wrong function.

    (For instance using an affine function for a projective scheme or a finite
    field function for a scheme defined over an infinite field.)

EXAMPLES:

Affine, over `\QQ`::

    sage: from sage.schemes.affine.affine_rational_point import enum_affine_rational_field
    sage: A.<x,y,z> = AffineSpace(3, QQ)
    sage: S = A.subscheme([2*x-3*y])
    sage: enum_affine_rational_field(S, 2)
    [(0, 0, -2), (0, 0, -1), (0, 0, -1/2), (0, 0, 0),
     (0, 0, 1/2), (0, 0, 1), (0, 0, 2)]


Affine, over a quadratic field::


AUTHORS:

- Angelos Koutsianas <koutsis.jr@gmail.com>: original version

"""

from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.padics.factory import Qp
from sage.sets.primes import Primes
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.schemes.affine.affine_space import AffineSpace
from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.modules.free_module_element import vector
from sage.schemes.affine.affine_rational_point import enum_affine_rational_field, enum_affine_number_field
from sage.schemes.projective.projective_rational_point import enum_projective_rational_field, enum_projective_number_field


class RationalPoints:
    """
    Computes the rational points on the curve of the given height_bound over the base field of the curve.

    INPUT:

    - ``C`` -  a curve.
    - ``height_bound`` -  a positive integer bound.

    OUTPUT:

    - a list containing the points of ``X`` of height up to ``B`` sorted.

    """

    def __init__(self, C, height_bound):
        self.C = C
        self.height_bound = height_bound
        self.basis_ring = C.base_ring()

    def get_points(self):
        pass


class RationalPointsAffineCurve(RationalPoints):
    """
        Computes the rational points on the affine curve of the given height_bound over the base field of the curve.

        INPUT:

        - ``C`` -  a curve.
        - ``height_bound`` -  a positive integer bound.
        - ``tolerance`` - a rational number in (0,1] used in doyle-krumm algorithm-4
        - ``prec`` - the precision to use for computing the elements of bounded height of number fields.
        - ``p`` - a given prime that we use in the hyperplane method.

        OUTPUT:

        - a list containing the points of ``X`` of (hyperplane) height up to ``height_bound`` sorted.

    """

    def __init__(self, C, height_bound, prec=50, **kwargs):
        super().__init__(C, height_bound)
        self.defining_polynomials = list(C.defining_polynomials())
        self._kwargs = kwargs
        self.prec = prec

    def get_points(self, method='naive'):
        if method == 'naive':
            if self.basis_ring == QQ:
                return enum_affine_rational_field(self.C, self.height_bound)
            else:
                return enum_affine_number_field(self.C, precision=self.prec, **self._kwargs)
        elif method == 'hyperplane':
            if self.basis_ring == QQ:
                if 'p' not in self._kwargs.keys():
                    raise ValueError('There is no given prime p')
                rpachrf = RationalPointsAffineCurveHyperplaneRationalField(
                    self.C,
                    self.height_bound,
                    p=self._kwargs['p'],
                    prec=self.prec
                )
                return rpachrf.get_small_height_points()
            else:
                return []
        else:
            raise NotImplementedError('There is no other method implemented!')


class RationalPointsAffineCurveHyperplaneRationalField(RationalPointsAffineCurve):
    """
        Computes the rational points on the affine curve of the given hyperplane height_bound over the base field of the
        curve.

        INPUT:

        - ``C`` -  a curve.
        - ``height_bound`` -  a positive integer bound.
        - ``p`` - a given prime that we use in the hyperplane method.
        - ``prec`` - the precision of the p-adic numbers


        OUTPUT:
            - a list containing the points of ``X`` of hyperplane height up to ``height_bound`` sorted.
    """

    def __init__(self, C, height_bound, p, prec=100, **kwargs):
        super().__init__(C, height_bound)
        self.p = p
        self.prec = prec
        self.Qp = Qp(p, prec=prec)
        if p not in Primes():
            raise ValueError('The number p is not a prime!')
        self.Cp = C.change_ring(FiniteField(p))
        if not self.Cp.is_smooth():
            raise ValueError('The reduction curve Cp is not smooth.')
        self.pts_modp = self.Cp.rational_points()
        self._kwargs = kwargs
        self._powers = [p**i for i in range(prec+2)]

    def get_small_height_points(self):
        pts = []
        An = self.C.ambient_space()
        hyperplanes = self._get_hyperplanes()
        for hyperplane in hyperplanes:
            polys = self.defining_polynomials + [hyperplane]
            S = An.subscheme(polys)
            Sp = S.change_ring(FiniteField(self.p))
            Sp_points = Sp.rational_points()
            if len(Sp_points):
                for barP in Sp_points:
                    try:
                        P = self._lift_point(S, barP)
                        if P:
                            P = [self._apply_LLL(ai) for ai in P]
                            if len([1 for f in self.defining_polynomials if f(P) != 0]) == 0:
                                if P not in pts:
                                    pts.append(P)
                    except Exception:
                        pass
        return pts

    def _get_hyperplanes(self):
        n = self.C.ambient_space().dimension()
        xis = list(self.C.ambient_space().gens())
        xis.append(1)
        An = ProjectiveSpace(ZZ, n-1)
        his = enum_projective_rational_field(An, self.height_bound)
        hyperplanes = [sum([xi * ai for xi, ai in zip(xis, hi)]) for hi in his]
        return hyperplanes

    def _lift_point(self, S, barP):
        polys = S.defining_polynomials()
        x1 = [QQ(ai) for ai in barP]
        Jac = S.Jacobian_matrix()
        if ZZ(Jac(x1).determinant()) % self.p == 0:
            return None
        A = Jac(x1).inverse()
        for i in range(1, self.prec + 1):
            y1 = A * (vector([-f(x1)/self._powers[i] for f in polys]))
            x1 = list(vector(x1) + self._powers[i] * y1)
            x1 = [ai % self._powers[i+1] for ai in x1]
        return x1

    def _apply_LLL(self, a):
        A = Matrix(ZZ, 2, [1, a, 0, self._powers[self.prec+1]])
        M = A.LLL()
        return M[0, 1]/M[0, 0]
