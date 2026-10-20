module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic intersections and unions

The scheme-theoretic intersection of two closed subschemes is cut out by the supremum of
their ideal sheaves, while their scheme-theoretic union is cut out by the infimum.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The scheme-theoretic intersection of two closed subschemes is cut out by the supremum
of their ideal sheaves. -/
@[stacks 0C4H "scheme-theoretic intersection"]
noncomputable abbrev schemeTheoreticIntersection (I J : X.IdealSheafData) : Scheme :=
  (I ⊔ J).subscheme

/-- The scheme-theoretic intersection is the subscheme attached to the supremum ideal sheaf. -/
@[simp] theorem schemeTheoreticIntersection_eq_subscheme_sup (I J : X.IdealSheafData) :
    schemeTheoreticIntersection I J = (I ⊔ J).subscheme := rfl

/-- The scheme-theoretic union of two closed subschemes is cut out by the infimum of their
ideal sheaves. -/
@[stacks 0C4H "scheme-theoretic union"]
noncomputable abbrev schemeTheoreticUnion (I J : X.IdealSheafData) : Scheme :=
  (I ⊓ J).subscheme

/-- The scheme-theoretic union is the subscheme attached to the infimum ideal sheaf. -/
@[simp] theorem schemeTheoreticUnion_eq_subscheme_inf (I J : X.IdealSheafData) :
    schemeTheoreticUnion I J = (I ⊓ J).subscheme := rfl

end AlgebraicGeometry.Scheme
