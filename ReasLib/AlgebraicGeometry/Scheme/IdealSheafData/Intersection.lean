module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic intersections as fiber products

The subscheme determined by the supremum of two ideal sheaf data is their scheme-theoretic
intersection, and its canonical square over the ambient scheme is cartesian.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The subscheme determined by `I ⊔ J` is the fiber product of the subschemes determined by
`I` and `J` over their ambient scheme. -/
@[stacks 0C4I "pullback square"]
theorem schemeTheoreticIntersection_isPullback :
    IsPullback
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J))
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J))
      J.subschemeι
      I.subschemeι := sorry

end AlgebraicGeometry
