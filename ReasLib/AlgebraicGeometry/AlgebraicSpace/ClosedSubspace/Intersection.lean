module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Inclusion

/-!
# Scheme-theoretic intersections of closed subspaces

The closed subspace cut out by the sum of two quasi-coherent ideal sheaves is
the fibre product of their closed subspaces over the ambient algebraic space.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]

/-- The canonical square from the closed subspace cut out by `I ⊔ J` to the
closed subspaces cut out by `I` and `J` is cartesian over the ambient algebraic
space. -/
theorem schemeTheoreticIntersection_isPullback :
    IsPullback (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion (le_sup_left : I ≤ I ⊔ J)) (subschemeι J) (subschemeι I) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
