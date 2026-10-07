module

public import ReasLib.AlgebraicGeometry.AffinePlane.Blowup
import StacksCheckRecall

/-!
# Blowup of the affine plane at the origin: strict transforms

This file records the three clauses of Exercise 111.27.8 on `A = k[x, y]`:
the strict transforms of the coordinate axes in the blowup along `(x, y)` are
disjoint, those of `V(x)` and the parabola `V(x - y^2)` are not, and the
explicit ideal `J = (x, y^2)` has the same vanishing locus as `(x, y)` while
separating the latter pair.
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial ReesAlgebra PrimeSpectrum

/- Exercise 111.27.8 (1): the strict transforms of the two coordinate divisors
in the blowup along `(x, y)` are disjoint. -/
@[stacks 02ED] #check (AlgebraicGeometry.AffinePlane.disjoint_strictTransform_xAxis_yAxis :
  ∀ (k : Type u) [Field k],
    Disjoint (strictTransform (MvPolynomial.idealOfVars (Fin 2) k) (zeroLocus {X 0}))
      (strictTransform (MvPolynomial.idealOfVars (Fin 2) k) (zeroLocus {X 1})))

/- Exercise 111.27.8 (2): the strict transforms of `V(x)` and `V(x - y²)`
in the blowup along `(x, y)` are not disjoint. -/
@[stacks 02ED] #check (AlgebraicGeometry.AffinePlane.not_disjoint_strictTransform_xAxis_parabola :
  ∀ (k : Type u) [Field k],
    ¬ Disjoint (strictTransform (MvPolynomial.idealOfVars (Fin 2) k) (zeroLocus {X 0}))
      (strictTransform (MvPolynomial.idealOfVars (Fin 2) k)
        (zeroLocus {AlgebraicGeometry.AffinePlane.parabola k})))

/- Exercise 111.27.8 (3): the explicit ideal `(x, y²)` has the same vanishing
locus as `(x, y)` and separates the strict transforms of `V(x)` and `V(x - y²)`. -/
@[stacks 02ED] #check (AlgebraicGeometry.AffinePlane.separatingIdeal_spec :
  ∀ (k : Type u) [Field k],
    zeroLocus (AlgebraicGeometry.AffinePlane.separatingIdeal k :
        Set (MvPolynomial (Fin 2) k)) =
      zeroLocus (MvPolynomial.idealOfVars (Fin 2) k : Set (MvPolynomial (Fin 2) k)) ∧
    Disjoint (strictTransform (AlgebraicGeometry.AffinePlane.separatingIdeal k)
        (zeroLocus {X 0}))
      (strictTransform (AlgebraicGeometry.AffinePlane.separatingIdeal k)
        (zeroLocus {AlgebraicGeometry.AffinePlane.parabola k})))
