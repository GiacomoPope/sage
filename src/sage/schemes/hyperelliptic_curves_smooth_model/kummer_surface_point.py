r"""
Points on a Kummer surface


AUTHORS:

- Sabrina Kunzweiler, Gareth Ma, Giacomo Pope (2024): adapt to smooth model
"""

# ****************************************************************************
#  Copyright (C) 2024 Sabrina Kunzweiler, Gareth Ma, Giacomo Pope
#  Distributed under the terms of the GNU General Public License (GPL)
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.rings.integer import Integer
from sage.schemes.hyperelliptic_curves_smooth_model.jacobian_morphism import MumfordDivisorClassField
from sage.modules.free_module_element import vector
from sage.structure.sage_object import SageObject


class KummerSurfacePoint(SageObject):
    r"""
    Point on a Kummer surface.

    TODO: 
    - Inheritance should be changed to Element (instead of SageObject),
    create Kummer homset ?
    - Most of the arithmetic is only implemented for curves of the form
    y^2 = f(x) at the moment.

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

            sage: R.<x> = FiniteField(13)[]
            sage: H = HyperellipticCurveSmoothModel(x^6 + 11*x^4 + 6*x^3 + 10*x^2 + 11*x + 1)
            sage: J = Jacobian(H)
            sage: K = KummerSurface(J)
            sage: D1 = K([1,11,9,1])
            sage: P1 = J(x^2 + 2*x + 9, 4*x + 4)
            sage: D1 == K(P1)
            True
            sage: 5*D1
            (10 : 5 : 9 : 5)
            sage: 10*D1 == K.zero()
            True

            sage: P2 = J(x + 11, 0)
            sage: D2 = K(P2)
            sage: D3 = K(P1-P2)
            sage: D1.differential_add(D2, D3)
            (12 : 8 : 9 : 12)
        """
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
        self._bij = [0,0,0] #is updated once a differential addition is performed

    def __repr__(self):
        r"""
        String representation of a point on the Kummer surface.

        TODO: Should this output normalized coordinates?

        EXAMPLES::

        """
        return f"({self._X0} : {self._X1} : {self._X2} : {self._X3})"

    def __eq__(self, other):
        r"""
        Equality of two points on the Kummer surface.
        """
        if self.parent() != other.parent():
            return False

        return self.normalize().coordinates() == other.normalize().coordinates()

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

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: H = HyperellipticCurveSmoothModel(x^6 + 4*x^5 + 10*x^4 + 6*x^3 + x^2 + 2*x + 1)
            sage: J = H.jacobian()
            sage: K = J.kummer_surface()
            sage: P = J(x + 1, -1)
            sage: Q = J(x^2 + x, 2*x + 1)
            sage: D1 = K(P)
            sage: D2 = D1.double().double()
            sage: D2.normalize()
            (3/55 : 1/55 : -3/22 : 1)
            sage: D2 == K(4*P)
            True
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

    def _evaluate_B(self, Q, index):
        """
        For a points self and Q, compute (Bij(P,Q))_j, where (Bij)_j is the row specified by index of 
        the matrix B used in differential additions.
        """
        x0, x1, x2, x3 = self.coordinates()
        bi0, bi1, bi2, bi3 = self._kummer._compute_biquadratic_forms()[index]
        v = vector(self._base_ring, [x0*x0, x0*x1, x1*x1, x0*x2, x1*x2, x2*x2, x0*x3, x1*x3, x2*x3, x3*x3])
        y0, y1, y2, y3 = Q.coordinates()
        w = vector(self._base_ring, [y0*y0, y0*y1, y1*y1, y0*y2, y1*y2, y2*y2, y0*y3, y1*y3, y2*y3, y3*y3])
        Bi0 = (bi0 * v) * w
        Bi1 = (bi1 * v) * w
        Bi2 = (bi2 * v) * w
        Bi3 = (bi3 * v) * w

        return Bi0, Bi1, Bi2, Bi3

    def differential_add(self, Q, PQ):
        r"""
        Return the differential addition of `K(P)`, `K(Q)` and `K(P-Q)` assuming none is the point at infinity.

        EXAMPLES::

        sage: R.<x> = QQ[]
        sage: H = HyperellipticCurveSmoothModel(x^6 + 4*x^5 + 10*x^4 + 6*x^3 + x^2 + 2*x + 1)
        sage: J = H.jacobian()
        sage: K = J.kummer_surface()
        sage: P = J(x + 1, -1)
        sage: Q = J(x^2 + x, 2*x + 1)
        sage: D1 = K(P)
        sage: D2 = K(Q)
        sage: D3 = K(P-Q)
        sage: D4 = D1.differential_add(D2, D3); D4
        (256 : 0 : 0 : 0)
        sage: D4 == K(P+Q)
        True

        sage: S = J(x^2 - 1/3*x - 5/2, 103/18*x + 31/6)
        sage: T2 = K(S)
        sage: T3 = K(P-S)
        sage: T4 = D1.differential_add(T2,T3)
        sage: T4.normalize()
        (5/11 : -155/308 : 57/308 : 1)
        sage: T4 == K(P+S)
        True
        """
        
        if PQ.is_zero():
            return self.double()
        elif self.is_zero() or Q.is_zero():
            return PQ
        z = PQ.coordinates()
        # We only need one row of the matrix B containing the biquadratic forms,
        # corresponding to a nonzero coordinate of PQ.
        if z[0] != 0:
            index = 0
            #z = [z[i]/z[0] for i in range(4)]
        elif z[1] != 0:
            index = 1
        else:
            index = 2

        Bi = self._evaluate_B(Q, index)
        x = [0,0,0,0]
        x[index] = Bi[index]
        x[index+1] = 2*Bi[index+1]*z[index] - x[index] * z[index+1]
        x[(index+2) % 4] = 2*Bi[(index+2) % 4]*z[index] - x[index] * z[(index+2) % 4]
        x[(index+3) % 4] = 2*Bi[(index+3) % 4]*z[index] - x[index] * z[(index+3) % 4]
        x[index] = x[index]*z[index]
        
        return self._kummer(x)

    def __mul__(self, m):
        r"""
        Montgomery-ladder to compute `m*P`.

        INPUT: `m` -- scalar to multiply `P` by.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: H = HyperellipticCurveSmoothModel(x^6 - 2*x^4 + 6*x^3 - 3*x^2 - 2*x + 1)
            sage: J = Jacobian(H)
            sage: K = KummerSurface(J)
            sage: P = J(x, -1)
            sage: K(100*P) == 100*K(P)
            True      
        """
        if not isinstance(m, (int, Integer)):
            try:
                m = Integer(m)
            except TypeError:
                raise TypeError(f"cannot coerce input scalar {m = } to an integer")

        # If m is zero, return identity
        if not m:
            return self._parent.zero()

        # [m]P = [-m]P on the Kummer surface
        m = abs(m)

        # Initialise for loop
        P0 = self._kummer([0,0,0,1])
        P1 = self

        # Montgomery ladder
        for bit in bin(m)[2:]:
            if bit == "0":
                P1 = P1.differential_add(P0, self)
                P0 = P0.double()
            else:
                P0 = P1.differential_add(P0, self)
                P1 = P1.double() 
        return P0

    def __rmul__(self, m):
        return self * m