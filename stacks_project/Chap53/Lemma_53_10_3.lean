module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.PlaneCurve
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.10.3: a proper genus-zero Gorenstein curve over a field with only constant global
functions is isomorphic over that field to a plane curve of degree two. -/
@[stacks 0C6N] #check
  (AlgebraicGeometry.SchemeOverField.exists_planeCurve_degree_two_of_genus_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
      [Scheme.Gorenstein X.left]
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_genus : SchemeOverField.genus X (topologicalKrullDim_eq_one X) hΓ = 0),
      ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
        (F : MvPolynomial (Fin 3) k),
        Nonempty (X ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
          HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2)

end AlgebraicGeometry.SchemeOverField
