r"""
Kummer surfaces over a general ring

Adapted from /hyperelliptic/kummer_surface.py

AUTHORS:

- David Kohel (2006): initial version
- Sabrina Kunzweiler, Gareth Ma, Giacomo Pope (2024): adapt to smooth model
"""

# ****************************************************************************
#  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>
#                2024 Sabrina Kunzweiler, Gareth Ma, Giacomo Pope
#  Distributed under the terms of the GNU General Public License (GPL)
#                  https://www.gnu.org/licenses/
# ****************************************************************************


from sage.schemes.projective.projective_space import ProjectiveSpace
from sage.schemes.projective.projective_subscheme import AlgebraicScheme_subscheme_projective
from sage.categories.homset import Hom
from sage.categories.schemes import Schemes
from sage.schemes.hyperelliptic_curves_smooth_model.jacobian_morphism import MumfordDivisorClassField
from sage.structure.sage_object import SageObject
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector




class KummerSurface(AlgebraicScheme_subscheme_projective):
    r"""
    Kummer surface of the Jacobian of a genus-2 curve.

    EXAMPLES::

    """

    def __init__(self, J):
        r"""
        Constructer for a Kummer surface of the Jacobian of a genus-2 curve.

        The equation for the Kummer surface is based on the code provided in 
        https://people.maths.ox.ac.uk/flynn/genus2/kummer/ with the modifications
        outlined in doi:10.1112/S1461157008000156 
        It works in any characteristic.

        EXAMPLES::
            sage: R.<x> = QQ[]
            sage: f = x**5 + x + 1
            sage: X = HyperellipticCurveSmoothModel(f)
            sage: J = Jacobian(X)
            sage: K = KummerSurface(J); K
            Closed subscheme of Projective Space of dimension 3 over Rational Field defined by:
            X0**4 - 4*X0*X1**3 + 4*X0**2*X1*X2 - 4*X0*X1**2*X2 + 2*X0**2*X2**2 + X2**4 + 4*X0**3*X3 + 2*X0**2*X1*X3 + 2*X1*X2**2*X3 + X1**2*X3**2 - 4*X0*X2*X3**2
        """

        self._jacobian = J
        self._curve = J.curve()
        self._base_ring = J.base_ring()

        PP = ProjectiveSpace(3, self._base_ring, ["X0", "X1", "X2", "X3"])
        X0, X1, X2, X3 = PP.gens()
        f, h = self._curve.hyperelliptic_polynomials()
        [h0,h1,h2,h3] = [h[i] for i in range(4)]
        [f0,f1,f2,f3,f4,f5,f6] = [f[i] for i in range(7)]

        K2 = (X1**2 - 4*X0*X2)

        K1 = (4*f0 + h0**2)*X0**3 + (2*f1 + h0*h1)*X0**2*X1 + (h0*h2)*X0*X1**2 + \
        (h0*h3)*X1**3 + (4*f2 - 2*h0*h2 + h1**2)*X0**2*X2 + \
        (2*f3 - 3*h0*h3 + h1*h2)*X0*X1*X2 + (h1*h3)*X1**2*X2 + \
        (4*f4 - 2*h1*h3 + h2**2)*X0*X2**2 + (2*f5 + h2*h3)*X1*X2**2 + (4*f6 + h3**2)*X2**3


        K0 = (-4*f0*f2 - f0*h1**2 + f1**2 + f1*h0*h1 - f2*h0**2)*X0**4 + \
            (-4*f0*f3 - 2*f0*h1*h2 + f1*h0*h2 - f3*h0**2)*X0**3*X1 + \
            (-4*f0*f4 - 2*f0*h1*h3 - f0*h2**2 + f1*h0*h3 - f4*h0**2)*X0**2*X1**2 + \
            (-4*f0*f5 - 2*f0*h2*h3 - f5*h0**2)*X0*X1**3 + \
            (-4*f0*f6 - f0*h3**2 - f6*h0**2)*X1**4 + \
            (2*f0*h1*h3 - 2*f1*f3 - f1*h0*h3 - f1*h1*h2 + 2*f2*h0*h2 - f3*h0*h1)*X0**3*X2 + \
            (4*f0*f5 + 2*f0*h2*h3 - 4*f1*f4 - f1*h1*h3 - f1*h2**2 + 2*f2*h0*h3 + f3*h0*h2 - 2*f4*h0*h1 + f5*h0**2)*X0**2*X1*X2 + \
            (8*f0*f6 + 2*f0*h3**2 - 4*f1*f5 - 2*f1*h2*h3 + f3*h0*h3 - 2*f5*h0*h1 + 2*f6*h0**2)*X0*X1**2*X2 + \
            (-4*f1*f6 - f1*h3**2 - 2*f6*h0*h1)*X1**3*X2 + \
            (-4*f0*f6 - f0*h3**2 + 2*f1*f5 + f1*h2*h3 - 4*f2*f4 - f2*h2**2 + f3**2 + f3*h0*h3 + f3*h1*h2 - f4*h1**2 + f5*h0*h1 - f6*h0**2)*X0**2*X2**2 + \
            (4*f1*f6 + f1*h3**2 - 4*f2*f5 - 2*f2*h2*h3 + f3*h1*h3 + 2*f4*h0*h3 - f5*h0*h2 - f5*h1**2 + 2*f6*h0*h1)*X0*X1*X2**2 + \
            (-4*f2*f6 - f2*h3**2 + f5*h0*h3 - 2*f6*h0*h2 - f6*h1**2)*X1**2*X2**2 + \
            (-2*f3*f5 - f3*h2*h3 + 2*f4*h1*h3 - f5*h0*h3 - f5*h1*h2 + 2*f6*h0*h2)*X0*X2**3 + \
            (-4*f3*f6 - f3*h3**2 + f5*h1*h3 - 2*f6*h1*h2)*X1*X2**3 + \
            (-4*f4*f6 - f4*h3**2 + f5**2 + f5*h2*h3 - f6*h2**2)*X2**4

        G = K2*X3**2 - K1*X3 + K0

        self._defining_equation = G
        self._simplified_model = None
        self._deltas = None
        self._b00 = None
        self._b01 = None
        self._b02 = None
        self._b03 = None

        AlgebraicScheme_subscheme_projective.__init__(self, PP, G)
        J._kummer_surface = self

    def __repr__(self):
        r"""
        String representation of the Kummer surface.

        EXAMPLES::
        """
        return f"Kummer Surface of {self._jacobian}. The defining equation is {self._defining_equation}"

    def __call__(self, P):
        r"""
        Create a point on the Kummer surface.

        INPUT: ``P`` -- either a point `P` on the Jacobian or
        coordinates `(X0, X1, X2, X3)` defining a point on the Kummer surface

        OUTPUT: A point on the Kummer surface.
        """
        return KummerSurfacePoint(self, P)

    def defining_equation(self):
        return self._defining_equation

    def jacobian(self):
        return self._jacobian

    def curve(self):
        return self._curve

    def defining_equation(self):
        return self._defining_equation

    def jacobian(self):
        return self._jacobian

    def curve(self):
        return self._curve

    def simplified_model(self):
        """
        Computes the simplified model of the Kummer surface 
        associated to the curve equation `y**2 = 4*f(x) - h(x)**2`.

        This only works if characteristic of the base field is not 2.
        """
        from sage.schemes.hyperelliptic_curves_smooth_model.hyperelliptic_constructor import HyperellipticCurveSmoothModel

        C = self.curve()
        f,h = C.hyperelliptic_polynomials()
        [h0,h1,h2,h3] = [h[i] for i in range(4)]
        F = 4*f - h**2
        Cp = HyperellipticCurveSmoothModel(F)
        Kp = Cp.jacobian().kummer_surface()
        self._simplified_model = Kp
        #auxiliary values to translate from one model to the other
        self._tau1 = [-2*h0*h2, -2*h0*h3, -2*h1*h2, 4*x3]
        self._tau2 = [h0*h2/2, h0*h3/2, h1*h2/2, x3/4]
        return Kp

    def _compute_deltas(self):
        """
        Computes the polynomials delta_1, delta_2, delta_3, delta_4
        that define doubling on the Kummer surface. 
        This requires an equation of the form y**2 = f(x)

        The polynomials are represented as a list of coefficients
        corresponding to the 35 monomials of degree 4

        [X3**4, X2*X3**3, X1*X3**3, ..., X0**3*X1, X0**4]

        Formulas for the delta_i are taken from 
        https://people.maths.ox.ac.uk/flynn/genus2/kummer/
        """
        if self._deltas:
            return self._deltas
        f, h = self._curve.hyperelliptic_polynomials()
        assert h == 0

        [f0,f1,f2,f3,f4,f5,f6] = [f[i] for i in range(7)]

        # note that delta1, delta2, delta3, delta4 are only computed once.
        delta0 = [0, 
            0, 
            0, 
            4, 
            (-12) * f6, 
            (-4) * f5, 
            0, 
            0, 
            0, 
            (4) * f2, 
            (-8) * (-f5**2 + 4*f4*f6), 
            (-24) * f6 * f3, 
            (-4) * (f3*f5 + 4*f2*f6), 
            (-16) * f6 * f2, 
            (-8) * (f2*f5 + 3*f1*f6), 
            (-8) * f5 * f1, 
            (-8) * f6 * f1, 
            (-4) * (f1*f5 + 12*f0*f6), 
            (-32) * f5 * f0, 
            (4) * (f1*f3 - 4*f0*f4), 
            (4) * (f4*f5**2 - 4*f4**2*f6 + 2*f3*f5*f6 - 4*f2*f6**2), 
            (4) * (f3*f5**2 - 4*f3*f4*f6 - 8*f1*f6**2), 
            (-8) * f6 * (f3**2 + 2*f1*f5 - 4*f0*f6), 
            (4) * (f2*f5**2 - 4*f2*f4*f6 - 2*f1*f5*f6 - 12*f0*f6**2), 
            (-8) * (f1*f5**2 + 2*f2*f3*f6 + 2*f0*f5*f6), 
            (-8) * (f1*f4*f5 - 2*f0*f5**2 + 2*f2**2*f6 - 3*f1*f3*f6 + 6*f0*f4*f6), 
            (-4) * (-f1*f5**2 + 4*f1*f4*f6 + 4*f0*f5*f6), 
            (-8) * (2*f0*f5**2 + 3*f1*f3*f6), 
            (-4) * (f1*f3*f5 + 4*f0*f4*f5 + 4*f1*f2*f6), 
            (16) * (-f0*f3*f5 - f1**2*f6 + 2*f0*f2*f6), 
            (-4) * f0 * (-f5**2 + 4*f4*f6), 
            (-32) * f6 * f3 * f0, 
            (-4) * (2*f0*f3*f5 - 3*f1**2*f6 + 16*f0*f2*f6), 
            (-8) * (-f1**2*f5 + 4*f0*f2*f5 + 2*f0*f1*f6), 
            (-4) * (-f0*f3**2 - f1**2*f4 + 4*f0*f2*f4 + 4*f0**2*f6)
        ]

        delta1 = [0,
            0,
            4,
            0,
            (4) * f5,
            (8) * f4,
            (-8) * f3,
            (5) * f3,
            (8) * f2,
            (4) * f1,
            (4) * f6 * f3,
            (2) * (f3*f5 + 8*f2*f6),
            (4) * (-3*f3*f4 + 4*f2*f5 - 4*f1*f6),
            (8) * (f2*f5 + f1*f6),
            (-2) * (5*f3**2 - 8*f2*f4 - 8*f1*f5 + 24*f0*f6),
            (4) * (-3*f2*f3 + 4*f1*f4 - 4*f0*f5),
            (4) * f5 * f1,
            (8) * (f1*f4 + f0*f5),
            (2) * (f1*f3 + 8*f0*f4),
            (4) * f3 * f0,
            f3*f5**2 - 4*f3*f4*f6 + 16*f1*f6**2,
            (4) * f6 * (-f3**2 + 4*f1*f5 + 8*f0*f6),
            (-2) * (3*f3**2*f5 - 8*f1*f5**2 - 8*f2*f3*f6 + 16*f1*f4*f6),
            (-4) * (-f1*f5**2 + f2*f3*f6 - 8*f0*f5*f6),
            (-4) * (3*f2*f3*f5 - 4*f1*f4*f5 - 8*f0*f5**2 - 8*f2**2*f6 + 5*f1*f3*f6 + 16*f0*f4*f6),
            (-1) * (-5*f3**3 + 20*f2*f3*f4 - 16*f1*f4**2 - 16*f2**2*f5 + 14*f1*f3*f5 + 20*f0*f3*f6),
            (-4) * (-2*f0*f5**2 + f1*f3*f6),
            (8) * (-f1*f3*f5 + 4*f0*f4*f5 + 4*f1*f2*f6 - 7*f0*f3*f6),
            (-4) * (3*f1*f3*f4 - 8*f0*f4**2 - 4*f1*f2*f5 + 5*f0*f3*f5 - 8*f1**2*f6 + 16*f0*f2*f6),
            (-2) * (3*f1*f3**2 - 8*f0*f3*f4 - 8*f1**2*f5 + 16*f0*f2*f5),
            (-4) * f6 * f3 * f0,
            (4) * (-f0*f3*f5 + 2*f1**2*f6),
            (4) * (-f0*f3*f4 + f1**2*f5 + 8*f0*f1*f6),
            (4) * f0 * (-f3**2 + 4*f1*f5 + 8*f0*f6),
            f1**2*f3 - 4*f0*f2*f3 + 16*f0**2*f5,
        ]

        delta2 = [0,
            4,
            0,
            0,
            (4) * f4,
            0,
            0,
            0,
            (-4) * f1,
            (-12) * f0,
            (4) * (f3*f5 - 4*f2*f6),
            (-32) * f6 * f1,
            (-8) * f5 * f1,
            (-4) * (f1*f5 + 12*f0*f6),
            (-8) * (f1*f4 + 3*f0*f5),
            (-4) * (f1*f3 + 4*f0*f4),
            (-8) * f5 * f0,
            (-16) * f4 * f0,
            (-24) * f3 * f0,
            (-8) * (-f1**2 + 4*f0*f2),
            (4) * (f2*f5**2 + f3**2*f6 - 4*f2*f4*f6 - 4*f0*f6**2),
            (-8) * (-f1*f5**2 + 4*f1*f4*f6 + 2*f0*f5*f6),
            (16) * (-f0*f5**2 - f1*f3*f6 + 2*f0*f4*f6),
            (-4) * (-3*f0*f5**2 + 2*f1*f3*f6 + 16*f0*f4*f6),
            (-4) * (f1*f3*f5 + 4*f0*f4*f5 + 4*f1*f2*f6),
            (-8) * (2*f0*f4**2 + f1*f2*f5 - 3*f0*f3*f5 - 2*f1**2*f6 + 6*f0*f2*f6),
            (-32) * f6 * f3 * f0,
            (-8) * (3*f0*f3*f5 + 2*f1**2*f6),
            (-8) * (2*f0*f3*f4 + f1**2*f5 + 2*f0*f1*f6),
            (8) * f0 * (-f3**2 - 2*f1*f5 + 4*f0*f6),
            (-4) * f6 * (-f1**2 + 4*f0*f2),
            (-4) * (-f1**2*f5 + 4*f0*f2*f5 + 4*f0*f1*f6),
            (-4) * (-f1**2*f4 + 4*f0*f2*f4 + 2*f0*f1*f5 + 12*f0**2*f6),
            (-4) * (-f1**2*f3 + 4*f0*f2*f3 + 8*f0**2*f5),
            (-4) * (-f1**2*f2 + 4*f0*f2**2 - 2*f0*f1*f3 + 4*f0**2*f4)
        ]

        delta3 = [1,
            0,
            0,
            0,
            (-2) * (f3*f5 - 4*f2*f6),
            (8) * f6 * f1,
            (16) * f6 * f0,
            (8) * f6 * f0,
            (8) * f5 * f0,
            (-2) * (f1*f3 - 4*f0*f4),
            (8) * (-f2*f5**2 - f3**2*f6 + 4*f2*f4*f6),
            (12) * f1 * (-f5**2 + 4*f4*f6),
            (8) * (-f0*f5**2 + 2*f1*f3*f6 + 4*f0*f4*f6),
            (8) * (-2*f0*f5**2 + f1*f3*f6 + 8*f0*f4*f6),
            (4) * f3 * (f1*f5 + 20*f0*f6),
            (8) * (2*f0*f3*f5 - f1**2*f6 + 4*f0*f2*f6),
            (16) * f6 * f3 * f0,
            (8) * (f0*f3*f5 - 2*f1**2*f6 + 8*f0*f2*f6),
            (12) * f5 * (-f1**2 + 4*f0*f2),
            (8) * (-f0*f3**2 - f1**2*f4 + 4*f0*f2*f4),
            f3**2*f5**2 - 4*f2*f4*f5**2 - 2*f1*f5**3 - 4*f3**2*f4*f6 + 16*f2*f4**2*f6 - 8*f2*f3*f5*f6 + 8*f1*f4*f5*f6 - 4*f0*f5**2*f6 + 16*f2**2*f6**2 - 16*f1*f3*f6**2 + 16*f0*f4*f6**2,
            (-8) * (f1*f4*f5**2 + f0*f5**3 - 4*f1*f4**2*f6 + 2*f1*f3*f5*f6 - 4*f0*f4*f5*f6 - 4*f1*f2*f6**2 + 4*f0*f3*f6**2),
            (-4) * (f1*f3*f5**2 - 4*f1*f3*f4*f6 - 4*f0*f3*f5*f6 - 8*f1**2*f6**2 + 16*f0*f2*f6**2),
            (-2) * (f1*f3*f5**2 + 8*f0*f4*f5**2 - 4*f1*f3*f4*f6 - 32*f0*f4**2*f6 + 12*f0*f3*f5*f6 - 8*f1**2*f6**2 - 16*f0*f2*f6**2),
            (-8) * (f0*f3*f5**2 - f1*f3**2*f6 - 8*f0*f3*f4*f6 - 2*f1**2*f5*f6 + 4*f0*f2*f5*f6 - 8*f0*f1*f6**2),
            (-4) * (-2*f0*f3*f4*f5 - 3*f1**2*f5**2 + 8*f0*f2*f5**2 - 2*f1*f2*f3*f6 + 4*f0*f3**2*f6 + 8*f1**2*f4*f6 - 24*f0*f2*f4*f6 - 16*f0**2*f6**2),
            (-8) * f0 * (f3*f5**2 - 4*f3*f4*f6 - 4*f1*f6**2),
            (16) * f6 * f0 * (3*f3**2 + 2*f1*f5 + 4*f0*f6),
            (-8) * (-f0*f3**2*f5 - 2*f0*f1*f5**2 + f1**2*f3*f6 - 8*f0*f2*f3*f6 + 4*f0*f1*f4*f6 - 8*f0**2*f5*f6),
            (-4) * (f1**2*f3*f5 - 4*f0*f2*f3*f5 - 8*f0**2*f5**2 - 4*f0*f1*f3*f6 + 16*f0**2*f4*f6),
            (-1) * (-f1**2*f5**2 + 4*f0*f2*f5**2 + 4*f1**2*f4*f6 - 16*f0*f2*f4*f6 - 16*f0**2*f6**2),
            (8) * f6 * (-f1**2*f3 + 4*f0*f2*f3 + 4*f0**2*f5),
            (2) * (-f1**2*f3*f5 + 4*f0*f2*f3*f5 + 8*f0**2*f5**2 - 8*f1**2*f2*f6 + 32*f0*f2**2*f6 - 12*f0*f1*f3*f6 + 16*f0**2*f4*f6),
            (-8) * (f1**2*f2*f5 - 4*f0*f2**2*f5 + 2*f0*f1*f3*f5 - 4*f0**2*f4*f5 + f1**3*f6 - 4*f0*f1*f2*f6 + 4*f0**2*f3*f6),
            f1**2*f3**2 - 4*f0*f2*f3**2 - 4*f1**2*f2*f4 + 16*f0*f2**2*f4 - 8*f0*f1*f3*f4 + 16*f0**2*f4**2 - 2*f1**3*f5 + 8*f0*f1*f2*f5 - 16*f0**2*f3*f5 - 4*f0*f1**2*f6 + 16*f0**2*f2*f6,
        ]
        self._deltas = delta0, delta1, delta2, delta3

        return delta0, delta1, delta2, delta3

    def _compute_bivariate_matrix(self, index):
        """
        This computes the auxiliary values to compute the matrix B
        satisfying b_ij(P, Q) = X_i(P+Q)*X_j(P-Q) + X_i(P-Q)*X_j(P+Q).
        More precisely, the output consists only on the row of B 
        specified by index.
        
        The matrix entries are degree-4 polynomials  
        b_ij in K[x0,x1,x2,x3,y0,y1,y2,y3], and we represent each 
        entry as a 10x10 matrix Mij with the property that 
        (x0**2, x0*x1, ... , x3**2) * Mij * (y0**2, y0*y1, ... , y3**2)

        The formulas are taken from https://people.maths.ox.ac.uk/flynn/genus2/kummer/biquadratic.forms
        """

        f, h = self._curve.hyperelliptic_polynomials()
        assert h == 0

        [f0,f1,f2,f3,f4,f5,f6] = [f[i] for i in range(7)]


        if index == 0:
            #compute the first row of the matrix B
            if not self._b00:
                self._b00 = Matrix(self._base_ring, [(0, 0, -4*f0*f6, 0, -4*f1*f6, -4*f2*f6, 0, 0, 0, 1),
                 (0, 8*f0*f6, 0, 4*f1*f6, 0, -4*f3*f6, 0, 0, -2*f5, 0),
                 (-4*f0*f6, 0, 0, 0, 0, f5**2 - 4*f4*f6, 0, 0, -4*f6, 0),
                 (0, 4*f1*f6, 0, 8*f2*f6, 4*f3*f6, 0, 0, 2*f5, 4*f6, 0),
                 (-4*f1*f6, 0, 0, 4*f3*f6, -2*f5**2 + 8*f4*f6, 0, 0, 4*f6, 0, 0),
                 (-4*f2*f6, -4*f3*f6, f5**2 - 4*f4*f6, 0, 0, 0, -4*f6, 0, 0, 0),
                 (0, 0, 0, 0, 0, -4*f6, -2, 0, 0, 0),
                 (0, 0, 0, 2*f5, 4*f6, 0, 0, 0, 0, 0),
                 (0, -2*f5, -4*f6, 4*f6, 0, 0, 0, 0, 0, 0),
                 (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b01:
                self._b01 = Matrix(self._base_ring, [(0, 0, 2*f0*f5, 0, 2*f1*f5 + 4*f0*f6, 2*f2*f5 + 2*f1*f6, 0, 0, f3, 0),
                 (0, -4*f0*f5, 0, -2*f1*f5 - 4*f0*f6, 2*f1*f6, f3*f5 + 4*f2*f6, 0, 0, 2*f4, 1),
                 (2*f0*f5, 0, 0, -2*f1*f6, 0, 2*f3*f6, 0, 0, f5, 0),
                 (0, -2*f1*f5 - 4*f0*f6, -2*f1*f6, -4*f2*f5 - 4*f1*f6, -f3*f5 - 4*f2*f6, 0, -f3, -2*f4, -2*f5, 0),
                 (2*f1*f5 + 4*f0*f6, 2*f1*f6, 0, -f3*f5 - 4*f2*f6, -4*f3*f6, 0, 0, -f5, -2*f6, 0),
                 (2*f2*f5 + 2*f1*f6, f3*f5 + 4*f2*f6, 2*f3*f6, 0, 0, 0, 2*f5, 2*f6, 0, 0),
                 (0, 0, 0, -f3, 0, 2*f5, 0, -1, 0, 0),
                 (0, 0, 0, -2*f4, -f5, 2*f6, -1, 0, 0, 0),
                 (f3, 2*f4, f5, -2*f5, -2*f6, 0, 0, 0, 0, 0),
                 (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b02:
                self._b02 = Matrix(self._base_ring, [(-f1**2 + 4*f0*f2, 2*f0*f3, 0, f1*f3, -2*f0*f5, -f1*f5, 2*f0, 0, 0, 0),
                 (2*f0*f3, 4*f0*f4, 2*f0*f5, 2*f1*f4, f1*f5 - 4*f0*f6, -2*f1*f6, f1, 0, 0, 0),
                 (0, 2*f0*f5, 4*f0*f6, f1*f5, 2*f1*f6, 0, 0, 0, 0, 0),
                 (f1*f3, 2*f1*f4, f1*f5, -f3**2 + 4*f2*f4 + 4*f0*f6, 2*f2*f5, f3*f5, 2*f2, f3, 2*f4, 1),
                 (-2*f0*f5, f1*f5 - 4*f0*f6, 2*f1*f6, 2*f2*f5, 4*f2*f6, 2*f3*f6, 0, 0, f5, 0),
                 (-f1*f5, -2*f1*f6, 0, f3*f5, 2*f3*f6, -f5**2 + 4*f4*f6, 0, 0, 2*f6, 0),
                 (2*f0, f1, 0, 2*f2, 0, 0, 0, 0, 1, 0),
                 (0, 0, 0, f3, 0, 0, 0, -1, 0, 0),
                 (0, 0, 0, 2*f4, f5, 2*f6, 1, 0, 0, 0),
                 (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b03:
                self._b03 = Matrix(self._base_ring, [(2*f0*f3**2 + 2*f1**2*f4 - 8*f0*f2*f4 - 8*f0**2*f6, 2*f1**2*f5 - 8*f0*f2*f5 - 4*f0*f1*f6, 2*f1**2*f6 - 8*f0*f2*f6, -4*f0*f3*f5 - 4*f1**2*f6 + 8*f0*f2*f6, -4*f0*f3*f6, 2*f0*f5**2 + 2*f1*f3*f6 - 8*f0*f4*f6, f1*f3 - 4*f0*f4, -2*f0*f5, -4*f0*f6, 0),
                 (2*f1**2*f5 - 8*f0*f2*f5 - 4*f0*f1*f6, -4*f0*f3*f5 + 2*f1**2*f6 - 16*f0*f2*f6, -8*f0*f3*f6, -f1*f3*f5 - 4*f0*f4*f5 - 4*f1*f2*f6 + 4*f0*f3*f6, -2*f0*f5**2 - 4*f1*f3*f6, -4*f0*f5*f6, -6*f0*f5, -f1*f5 - 4*f0*f6, -2*f1*f6, 0),
                 (2*f1**2*f6 - 8*f0*f2*f6, -8*f0*f3*f6, 2*f0*f5**2 - 8*f0*f4*f6, -2*f0*f5**2 - 2*f1*f3*f6, f1*f5**2 - 4*f1*f4*f6 - 4*f0*f5*f6, -8*f0*f6**2, -8*f0*f6, -2*f1*f6, 0, 0),
                 (-4*f0*f3*f5 - 4*f1**2*f6 + 8*f0*f2*f6, -f1*f3*f5 - 4*f0*f4*f5 - 4*f1*f2*f6 + 4*f0*f3*f6, -2*f0*f5**2 - 2*f1*f3*f6, -4*f1*f4*f5 + 4*f0*f5**2 - 8*f2**2*f6 + 8*f1*f3*f6 - 8*f0*f4*f6, -2*f1*f5**2 - 4*f2*f3*f6, -2*f3**2*f6 - 4*f1*f5*f6 + 8*f0*f6**2, -2*f1*f5 + 4*f0*f6, -2*f2*f5, -f3*f5 - 4*f2*f6, 0),
                 (-4*f0*f3*f6, -2*f0*f5**2 - 4*f1*f3*f6, f1*f5**2 - 4*f1*f4*f6 - 4*f0*f5*f6, -2*f1*f5**2 - 4*f2*f3*f6, 2*f2*f5**2 - 8*f2*f4*f6 - 4*f1*f5*f6 - 8*f0*f6**2, f3*f5**2 - 4*f3*f4*f6 - 8*f1*f6**2, -4*f1*f6, -4*f2*f6, -4*f3*f6, 0),
                 (2*f0*f5**2 + 2*f1*f3*f6 - 8*f0*f4*f6, -4*f0*f5*f6, -8*f0*f6**2, -2*f3**2*f6 - 4*f1*f5*f6 + 8*f0*f6**2, f3*f5**2 - 4*f3*f4*f6 - 8*f1*f6**2, 2*f4*f5**2 - 8*f4**2*f6 + 4*f3*f5*f6 - 8*f2*f6**2, 0, -2*f3*f6, 2*f5**2 - 8*f4*f6, 0),
                 (f1*f3 - 4*f0*f4, -6*f0*f5, -8*f0*f6, -2*f1*f5 + 4*f0*f6, -4*f1*f6, 0, 2*f2, 0, 0, 1),
                 (-2*f0*f5, -f1*f5 - 4*f0*f6, -2*f1*f6, -2*f2*f5, -4*f2*f6, -2*f3*f6, 0, 0, -f5, 0),
                 (-4*f0*f6, -2*f1*f6, 0, -f3*f5 - 4*f2*f6, -4*f3*f6, 2*f5**2 - 8*f4*f6, 0, -f5, -6*f6, 0),
                 (0, 0, 0, 0, 0, 0, 1, 0, 0, 0)]
                )
            bi0, bi1, bi2, bi3 = self._b00, self._b01, self._b02, self._b03
        if index == 1:
            if not self._b01:
                self._b01 = Matrix(self._base_ring, [(0, 0, 2*f0*f5, 0, 2*f1*f5 + 4*f0*f6, 2*f2*f5 + 2*f1*f6, 0, 0, f3, 0),
                 (0, -4*f0*f5, 0, -2*f1*f5 - 4*f0*f6, 2*f1*f6, f3*f5 + 4*f2*f6, 0, 0, 2*f4, 1),
                 (2*f0*f5, 0, 0, -2*f1*f6, 0, 2*f3*f6, 0, 0, f5, 0),
                 (0, -2*f1*f5 - 4*f0*f6, -2*f1*f6, -4*f2*f5 - 4*f1*f6, -f3*f5 - 4*f2*f6, 0, -f3, -2*f4, -2*f5, 0),
                 (2*f1*f5 + 4*f0*f6, 2*f1*f6, 0, -f3*f5 - 4*f2*f6, -4*f3*f6, 0, 0, -f5, -2*f6, 0),
                 (2*f2*f5 + 2*f1*f6, f3*f5 + 4*f2*f6, 2*f3*f6, 0, 0, 0, 2*f5, 2*f6, 0, 0),
                 (0, 0, 0, -f3, 0, 2*f5, 0, -1, 0, 0),
                 (0, 0, 0, -2*f4, -f5, 2*f6, -1, 0, 0, 0),
                 (f3, 2*f4, f5, -2*f5, -2*f6, 0, 0, 0, 0, 0),
                 (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b11:
                self._b11 = Matrix(self._base_ring, [(2*f1**2 - 8*f0*f2, -4*f0*f3, -4*f0*f4, -2*f1*f3, -4*f1*f4 - 4*f0*f5, f3**2 - 4*f2*f4 - 2*f1*f5 - 4*f0*f6, -4*f0, -2*f1, -4*f2, 0),
                 (-4*f0*f3, 0, -4*f0*f5, 8*f0*f5, -4*f1*f5, -4*f2*f5 - 4*f1*f6, 0, 0, -2*f3, 0),
                 (-4*f0*f4, -4*f0*f5, -8*f0*f6, 8*f0*f6, -4*f1*f6, -4*f2*f6, 0, 0, 0, 1),
                 (-2*f1*f3, 8*f0*f5, 8*f0*f6, 8*f1*f5, 8*f1*f6, -2*f3*f5, 0, 2*f3, 0, 0),
                 (-4*f1*f4 - 4*f0*f5, -4*f1*f5, -4*f1*f6, 8*f1*f6, 0, -4*f3*f6, -2*f3, 0, 0, 0),
                 (f3**2 - 4*f2*f4 - 2*f1*f5 - 4*f0*f6, -4*f2*f5 - 4*f1*f6, -4*f2*f6, -2*f3*f5, -4*f3*f6, 2*f5**2 - 8*f4*f6, -4*f4, -2*f5, -4*f6, 0),
                 (-4*f0, 0, 0, 0, -2*f3, -4*f4, 0, 0, -4, 0),
                 (-2*f1, 0, 0, 2*f3, 0, -2*f5, 0, 0, 0, 0),
                 (-4*f2, -2*f3, 0, 0, 0, -4*f6, -4, 0, 0, 0),
                 (0, 0, 1, 0, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b12:
                self._b12 = Matrix(self._base_ring, [(0, 0, 2*f0*f3, 0, f1*f3 + 4*f0*f4, 2*f1*f4 + 2*f0*f5, 0, 2*f0, 2*f1, 0),
                 (0, -4*f0*f3, 0, -f1*f3 - 4*f0*f4, 2*f0*f5, 2*f1*f5 + 4*f0*f6, -2*f0, -f1, 0, 0),
                 (2*f0*f3, 0, 0, -2*f0*f5, 0, 2*f1*f6, f1, 0, 0, 0),
                 (0, -f1*f3 - 4*f0*f4, -2*f0*f5, -4*f1*f4 - 4*f0*f5, -2*f1*f5 - 4*f0*f6, 0, -2*f1, -2*f2, -f3, 0),
                 (f1*f3 + 4*f0*f4, 2*f0*f5, 0, -2*f1*f5 - 4*f0*f6, -4*f1*f6, 0, 2*f2, 0, 0, 1),
                 (2*f1*f4 + 2*f0*f5, 2*f1*f5 + 4*f0*f6, 2*f1*f6, 0, 0, 0, f3, 0, 0, 0),
                 (0, -2*f0, f1, -2*f1, 2*f2, f3, 0, 0, 0, 0),
                 (2*f0, -f1, 0, -2*f2, 0, 0, 0, 0, -1, 0),
                 (2*f1, 0, 0, -f3, 0, 0, 0, -1, 0, 0),
                 (0, 0, 0, 0, 1, 0, 0, 0, 0, 0)]
                )
            if not self._bi3:
                self._b13 = Matrix(self._base_ring, [(-f1**2*f3 + 4*f0*f2*f3 + 8*f0**2*f5, 2*f0*f3**2 + 4*f0*f1*f5 + 8*f0**2*f6, 4*f0*f1*f6, 4*f0*f3*f4 + 4*f1**2*f5 - 8*f0*f2*f5, 4*f1**2*f6 - 8*f0*f2*f6, -f1*f3*f5, 4*f0*f3, f1*f3, 0, 0),
                 (2*f0*f3**2 + 4*f0*f1*f5 + 8*f0**2*f6, 4*f0*f3*f4 + 2*f1**2*f5 + 8*f0*f1*f6, 2*f0*f3*f5 + 2*f1**2*f6, 8*f0*f4**2 + 4*f1*f2*f5 - 8*f0*f3*f5 + 4*f1**2*f6 - 8*f0*f2*f6, f1*f3*f5 + 4*f0*f4*f5 + 4*f1*f2*f6 - 12*f0*f3*f6, 4*f0*f5**2 - 8*f0*f4*f6, f1*f3 + 4*f0*f4, 2*f1*f4, 2*f1*f5 - 4*f0*f6, 0),
                 (4*f0*f1*f6, 2*f0*f3*f5 + 2*f1**2*f6, 4*f0*f3*f6, 4*f0*f4*f5 + 4*f1*f2*f6 - 8*f0*f3*f6, 2*f0*f5**2 + 2*f1*f3*f6, 4*f0*f5*f6, 2*f0*f5, f1*f5, 2*f1*f6, 0),
                 (4*f0*f3*f4 + 4*f1**2*f5 - 8*f0*f2*f5, 8*f0*f4**2 + 4*f1*f2*f5 - 8*f0*f3*f5 + 4*f1**2*f6 - 8*f0*f2*f6, 4*f0*f4*f5 + 4*f1*f2*f6 - 8*f0*f3*f6, f3**3 - 4*f2*f3*f4 + 8*f1*f4**2 + 8*f2**2*f5 - 8*f1*f3*f5 - 4*f0*f3*f6, 4*f1*f4*f5 + 4*f0*f5**2 + 8*f2**2*f6 - 8*f1*f3*f6 - 8*f0*f4*f6, 4*f1*f5**2 + 4*f2*f3*f6 - 8*f1*f4*f6, 4*f1*f4 - 4*f0*f5, -f3**2 + 4*f2*f4 - 4*f0*f6, 4*f2*f5 - 4*f1*f6, 0),
                 (4*f1**2*f6 - 8*f0*f2*f6, f1*f3*f5 + 4*f0*f4*f5 + 4*f1*f2*f6 - 12*f0*f3*f6, 2*f0*f5**2 + 2*f1*f3*f6, 4*f1*f4*f5 + 4*f0*f5**2 + 8*f2**2*f6 - 8*f1*f3*f6 - 8*f0*f4*f6, 2*f1*f5**2 + 4*f2*f3*f6 + 8*f0*f5*f6, 2*f3**2*f6 + 4*f1*f5*f6 + 8*f0*f6**2, 2*f1*f5 - 4*f0*f6, 2*f2*f5, f3*f5 + 4*f2*f6, 0),
                 (-f1*f3*f5, 4*f0*f5**2 - 8*f0*f4*f6, 4*f0*f5*f6, 4*f1*f5**2 + 4*f2*f3*f6 - 8*f1*f4*f6, 2*f3**2*f6 + 4*f1*f5*f6 + 8*f0*f6**2, -f3*f5**2 + 4*f3*f4*f6 + 8*f1*f6**2, 0, f3*f5, 4*f3*f6, 0),
                 (4*f0*f3, f1*f3 + 4*f0*f4, 2*f0*f5, 4*f1*f4 - 4*f0*f5, 2*f1*f5 - 4*f0*f6, 0, 2*f1, 2*f2, f3, 0),
                 (f1*f3, 2*f1*f4, f1*f5, -f3**2 + 4*f2*f4 - 4*f0*f6, 2*f2*f5, f3*f5, 2*f2, f3, 2*f4, 1),
                 (0, 2*f1*f5 - 4*f0*f6, 2*f1*f6, 4*f2*f5 - 4*f1*f6, f3*f5 + 4*f2*f6, 4*f3*f6, f3, 2*f4, 2*f5, 0),
                 (0, 0, 0, 0, 0, 0, 0, 1, 0, 0)]
                )
            bi0, bi1, bi2, bi3 = self._b01, self._b11, self._b12, self._b13
        if index == 2:
            if not self._b02:
                self._b02 = Matrix(self._base_ring, [(-f1**2 + 4*f0*f2, 2*f0*f3, 0, f1*f3, -2*f0*f5, -f1*f5, 2*f0, 0, 0, 0),
                 (2*f0*f3, 4*f0*f4, 2*f0*f5, 2*f1*f4, f1*f5 - 4*f0*f6, -2*f1*f6, f1, 0, 0, 0),
                 (0, 2*f0*f5, 4*f0*f6, f1*f5, 2*f1*f6, 0, 0, 0, 0, 0),
                 (f1*f3, 2*f1*f4, f1*f5, -f3**2 + 4*f2*f4 + 4*f0*f6, 2*f2*f5, f3*f5, 2*f2, f3, 2*f4, 1),
                 (-2*f0*f5, f1*f5 - 4*f0*f6, 2*f1*f6, 2*f2*f5, 4*f2*f6, 2*f3*f6, 0, 0, f5, 0),
                 (-f1*f5, -2*f1*f6, 0, f3*f5, 2*f3*f6, -f5**2 + 4*f4*f6, 0, 0, 2*f6, 0),
                 (2*f0, f1, 0, 2*f2, 0, 0, 0, 0, 1, 0),
                 (0, 0, 0, f3, 0, 0, 0, -1, 0, 0),
                 (0, 0, 0, 2*f4, f5, 2*f6, 1, 0, 0, 0),
                 (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)]
                )
            if not self._b12:
                self._b12 = Matrix(self._base_ring, [(0, 0, 2*f0*f3, 0, f1*f3 + 4*f0*f4, 2*f1*f4 + 2*f0*f5, 0, 2*f0, 2*f1, 0),
                 (0, -4*f0*f3, 0, -f1*f3 - 4*f0*f4, 2*f0*f5, 2*f1*f5 + 4*f0*f6, -2*f0, -f1, 0, 0),
                 (2*f0*f3, 0, 0, -2*f0*f5, 0, 2*f1*f6, f1, 0, 0, 0),
                 (0, -f1*f3 - 4*f0*f4, -2*f0*f5, -4*f1*f4 - 4*f0*f5, -2*f1*f5 - 4*f0*f6, 0, -2*f1, -2*f2, -f3, 0),
                 (f1*f3 + 4*f0*f4, 2*f0*f5, 0, -2*f1*f5 - 4*f0*f6, -4*f1*f6, 0, 2*f2, 0, 0, 1),
                 (2*f1*f4 + 2*f0*f5, 2*f1*f5 + 4*f0*f6, 2*f1*f6, 0, 0, 0, f3, 0, 0, 0),
                 (0, -2*f0, f1, -2*f1, 2*f2, f3, 0, 0, 0, 0),
                 (2*f0, -f1, 0, -2*f2, 0, 0, 0, 0, -1, 0),
                 (2*f1, 0, 0, -f3, 0, 0, 0, -1, 0, 0),
                 (0, 0, 0, 0, 1, 0, 0, 0, 0, 0)]
                )
            if not self._b22:
                self._b22 = Matrix(self._base_ring, [(0, 0, f1**2 - 4*f0*f2, 0, -4*f0*f3, -4*f0*f4, 0, 0, -4*f0, 0),
                 (0, -2*f1**2 + 8*f0*f2, 0, 4*f0*f3, 0, -4*f0*f5, 0, 4*f0, 0, 0),
                 (f1**2 - 4*f0*f2, 0, 0, 0, 0, -4*f0*f6, -4*f0, 0, 0, 0),
                 (0, 4*f0*f3, 0, 8*f0*f4, 4*f0*f5, 0, 4*f0, 2*f1, 0, 0),
                 (-4*f0*f3, 0, 0, 4*f0*f5, 8*f0*f6, 0, -2*f1, 0, 0, 0),
                 (-4*f0*f4, -4*f0*f5, -4*f0*f6, 0, 0, 0, 0, 0, 0, 1),
                 (0, 0, -4*f0, 4*f0, -2*f1, 0, 0, 0, 0, 0),
                 (0, 4*f0, 0, 2*f1, 0, 0, 0, 0, 0, 0),
                 (-4*f0, 0, 0, 0, 0, 0, 0, 0, -2, 0),
                 (0, 0, 0, 0, 0, 1, 0, 0, 0, 0)]
                )
            if not self._b23:
                self._b23 = Matrix(self._base_ring, [(2*f1**2*f2 - 8*f0*f2**2 + 4*f0*f1*f3 - 8*f0**2*f4, f1**2*f3 - 4*f0*f2*f3 - 8*f0**2*f5, -8*f0**2*f6, -2*f0*f3**2 - 4*f0*f1*f5 + 8*f0**2*f6, -4*f0*f1*f6, 2*f0*f3*f5 + 2*f1**2*f6 - 8*f0*f2*f6, 2*f1**2 - 8*f0*f2, -2*f0*f3, 0, 0),
                 (f1**2*f3 - 4*f0*f2*f3 - 8*f0**2*f5, 2*f1**2*f4 - 8*f0*f2*f4 - 4*f0*f1*f5 - 8*f0**2*f6, f1**2*f5 - 4*f0*f2*f5 - 4*f0*f1*f6, -4*f0*f3*f4 - 2*f1**2*f5, -4*f0*f3*f5 - 2*f1**2*f6, -4*f0*f3*f6, -4*f0*f3, -4*f0*f4, -4*f0*f5, 0),
                 (-8*f0**2*f6, f1**2*f5 - 4*f0*f2*f5 - 4*f0*f1*f6, 2*f1**2*f6 - 8*f0*f2*f6, -2*f0*f3*f5 - 2*f1**2*f6, -8*f0*f3*f6, 2*f0*f5**2 - 8*f0*f4*f6, 0, -2*f0*f5, -8*f0*f6, 0),
                 (-2*f0*f3**2 - 4*f0*f1*f5 + 8*f0**2*f6, -4*f0*f3*f4 - 2*f1**2*f5, -2*f0*f3*f5 - 2*f1**2*f6, -8*f0*f4**2 - 4*f1*f2*f5 + 8*f0*f3*f5 + 4*f1**2*f6 - 8*f0*f2*f6, -f1*f3*f5 - 4*f0*f4*f5 - 4*f1*f2*f6 + 4*f0*f3*f6, -4*f0*f5**2 - 4*f1*f3*f6 + 8*f0*f4*f6, -f1*f3 - 4*f0*f4, -2*f1*f4, -2*f1*f5 + 4*f0*f6, 0),
                 (-4*f0*f1*f6, -4*f0*f3*f5 - 2*f1**2*f6, -8*f0*f3*f6, -f1*f3*f5 - 4*f0*f4*f5 - 4*f1*f2*f6 + 4*f0*f3*f6, 2*f0*f5**2 - 4*f1*f3*f6 - 16*f0*f4*f6, 2*f1*f5**2 - 8*f1*f4*f6 - 4*f0*f5*f6, -2*f0*f5, -f1*f5 - 4*f0*f6, -6*f1*f6, 0),
                 (2*f0*f3*f5 + 2*f1**2*f6 - 8*f0*f2*f6, -4*f0*f3*f6, 2*f0*f5**2 - 8*f0*f4*f6, -4*f0*f5**2 - 4*f1*f3*f6 + 8*f0*f4*f6, 2*f1*f5**2 - 8*f1*f4*f6 - 4*f0*f5*f6, 2*f2*f5**2 + 2*f3**2*f6 - 8*f2*f4*f6 - 8*f0*f6**2, -4*f0*f6, -2*f1*f6, f3*f5 - 4*f2*f6, 0),
                 (2*f1**2 - 8*f0*f2, -4*f0*f3, 0, -f1*f3 - 4*f0*f4, -2*f0*f5, -4*f0*f6, -6*f0, -f1, 0, 0),
                 (-2*f0*f3, -4*f0*f4, -2*f0*f5, -2*f1*f4, -f1*f5 - 4*f0*f6, -2*f1*f6, -f1, 0, 0, 0),
                 (0, -4*f0*f5, -8*f0*f6, -2*f1*f5 + 4*f0*f6, -6*f1*f6, f3*f5 - 4*f2*f6, 0, 0, 2*f4, 1),
                 (0, 0, 0, 0, 0, 0, 0, 0, 1, 0)]
                )
            bi0, bi1, bi2, bi3 = self._b02, self._b12, self._b22, self._b23
        return bi0, bi1, bi2, bi3

class KummerSurfacePoint(SageObject):
    r"""
    Point on a Kummer surface.

    EXAMPLES::

    """
    def __init__(self, kummer, P, check=True):
        r"""
        Create a point from the coordinates.

        INPUT:

            - ``kummer`` - A Kummer surface

            - ``coords`` - either a point P on the Jacobian, 
            or coordinates (x0,x1,x2,x3) defining a point on
            the Kummer surface

        EXAMPLES::

        """
        # Ensure the kummer is the right type
        if not isinstance(kummer, KummerSurface):
            raise TypeError("{kummer} is not a Kummer surface")

        R = kummer.base_ring()

        # neutral element
        if P == 0:
            P = (0,0,0,1)

        # Construct point from Mumford coordinates
        elif isinstance(P, MumfordDivisorClassField):
            J = P.parent().curve().jacobian() # easier way to access J ? 
            P = J.mumford_to_kummer(P)

        else:
            if not len(P) == 4:
                raise ValueError("The input must consist of 4 coordinates")
        
        # check that the coordinates are valid
        if check:
            if kummer.defining_equation()(P) != 0:
                raise ValueError("The coordinates do not define a valid point")

        self._base_ring = R
        self._kummer = kummer
        self._X0, self._X1, self._X2, self._X3 = P
        self._projective_point = P
        self._bij = [0,0,0] #is updated once a differential addition is performed


    def __repr__(self):
        r"""
        String representation of a point on the Kummer surface.

        EXAMPLES::

        """
        return f"({self._X0} : {self._X1} : {self._X2} : {self._X3})"

    def __eq__(self, other):
        r"""
        Equality of two points on the Kummer surface.
        """
        if self.parent() != other.parent():
            return False

        return self._projective_point == other._projective_point

    def base_ring(self):
        r"""
        Return the base ring of the point on the Kummer surface.

        EXAMPLES::
        """
        return self._base_ring

    def coordinates(self):
        r"""
        Return the coordinates of the point.
        """
        return self._X0, self._X1, self._X2, self._X3

    def is_zero(self):
        r"""
        The zero point is the image of the neutral element on the Kummer surface.
        """

        return self._X0 == self._X1 == self._X2 == 0

    def normalize(self):
        r"""
        Normalize the coordinates of self so that the last nonzero entry is one.
        """

        P = self._kummer.point(self.coordinates())
        return KummerSurfacePoint(self._kummer, list(P))

    def _degree_4_monomials(self):
        """
        Evaluate all degree-4 monomials at the point.
        """
        X0,X1,X2,X3 = self.coordinates()
        mons = [X3**4, X2*X3**3, X1*X3**3, X0*X3**3, X2**2*X3**2, X1*X2*X3**2, X0*X2*X3**2, X1**2*X3**2,
         X0*X1*X3**2, X0**2*X3**2, X2**3*X3, X1*X2**2*X3, X0*X2**2*X3, X1**2*X2*X3, X0*X1*X2*X3, 
         X0**2*X2*X3, X1**3*X3, X0*X1**2*X3, X0**2*X1*X3, X0**3*X3, X2**4, X1*X2**3, X0*X2**3, X1**2*X2**2, 
         X0*X1*X2**2, X0**2*X2**2, X1**3*X2, X0*X1**2*X2, X0**2*X1*X2, X0**3*X2, X1**4, X0*X1**3, X0**2*X1**2, X0**3*X1, X0**4]
        return mons


    def double(self):
        r"""
        Return the doubling of the point.
        """
        if self._base_ring.characteristic() == 2:
            raise NotImplementedError("Arithmetic on the Kummer surface is not implemented for characteristic 2.")
        K = self._kummer
        f, h = K._curve.hyperelliptic_polynomials()
        if h == 0:
            delta0, delta1, delta2, delta3 = K._compute_deltas()
            mons = self._degree_4_monomials()
            y0 = sum([delta0[i]*mons[i] for i in range(35)])
            y1 = sum([delta1[i]*mons[i] for i in range(35)])
            y2 = sum([delta2[i]*mons[i] for i in range(35)])
            y3 = sum([delta3[i]*mons[i] for i in range(35)])
            return KummerSurfacePoint(K, [y0,y1,y2,y3])
        else:
            if K._simplified_model:
                Kp = K._simplified_model
            else:
                Kp = K.simplified_model()
            tau1 = K._tau1
            tau2 = K._tau2
            delta0, delta1, delta2, delta3 = Kp._compute_deltas()

            # P  is transformed to a point on the simplified Kummer surface Kp
            x0,x1,x2,x3 = self.coordinates()
            Pp = KummerSurfacePoint(Kp, [x0,x1,x2,x3,tau1[0]*x0 + tau1[1]*x1 + tau1[2]*x2 + tau1[3]*x3])   
            
            #apply delta to the transformed point
            mons = Pp._degree_4_monomials()
            y0 = sum([delta0[i]*mons[i] for i in range(35)])
            y1 = sum([delta1[i]*mons[i] for i in range(35)])
            y2 = sum([delta2[i]*mons[i] for i in range(35)])
            y3 = sum([delta3[i]*mons[i] for i in range(35)])

            #transform back to K
            return KummerSurfacePoint(K, [y0,y1,y2,tau2[0]*y0 + tau2[1]*y1 + tau2[2]*y2 + tau2[3]*y3])

    def _evaluate_B_x(self, index):
        """
        For a point self = (x0,x1,x2,x3), compute Bij(x,y) =  (bij)_j * (x0**2, x0*x1, ..., x3*x3),
        the result are 4 vectors representing degree-2 polynomial in y0, ... , y3.

        Here (bij)_j represents the i-th row of the matrix B used in differential additions.
        """
        x0, x1, x2, x3 = self.coordinates()
        bi0, bi1, bi2, bi3 = self._kummer._compute_bivariate_matrix(index)
        v = vector(self._base_ring, [x0**2, x0*x1, x1**2, x0*x2, x1*x2, x2**2, x0*x3, x1*x3, x2*x3, x3**2])
        return bi0*v, bi1*v, bi2*v, bi3*v

    def _evaluate_B_xy(self, Q, index):
        """
        For a points self and Q, compute (Bij(P,Q))_j, where (Bij)_j is the row specified by index of 
        the matrix B used in differential additions.
        """
        y0, y1, y2, y3 = Q.coordinates()
        w = vector(self._base_ring, [y0**2, y0*y1, y1**2, y0*y2, y1*y2, y2**2, y0*y3, y1*y3, y2*y3, y3**2])
        if self._bij[index] == 0:
            self._bij[index] = self._evaluate_B_x(index)
        Bi0 = (self._bij[index][0]) * w
        Bi1 = (self._bij[index][1]) * w
        Bi2 = (self._bij[index][2]) * w
        Bi3 = (self._bij[index][3]) * w

        return Bi0, Bi1, Bi2, Bi3


    def differential_add(self, Q, PQ):
        r"""
        Return the differential addition of `K(P)`, `K(Q)` and `K(P-Q)` assuming none is the point at infinity.

        INPUT:

        EXAMPLES::

        """
        
        if PQ.is_zero():
            return self.double()
        elif self.is_zero() or Q.is_zero():
            return PQ
        z = PQ.coordinates()
        # We only need one row of the bilinear matrix B, corresponding to a nonzero coordinate of PQ.
        if z[0] != 0:
            index = 0
            #z = [z[i]/z[0] for i in range(4)]
        elif z[1] != 0:
            index = 1
        else:
            index = 2
        Bi = self._evaluate_B_xy(Q, index)
        x = [0,0,0,0]
        print(z[index])
        x[index] = Bi[index]
        x[index+1] = 2*Bi[index+1]*z[index] - x[index] * z[index+1]
        x[(index+2) % 4] = 2*Bi[(index+2) % 4]*z[index] - x[index] * z[(index+2) % 4]
        x[(index+3) % 4] = 2*Bi[(index+3) % 4]*z[index] - x[index] * z[(index+3) % 4]
        x[index] = x[index]*z[index]
        print(x)
        return self._kummer(x)



