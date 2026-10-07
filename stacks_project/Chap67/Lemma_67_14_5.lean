module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_14_5_Inclusion

/-!
# Lemma 67.14.5

Scheme-theoretic intersections of closed subspaces of algebraic spaces are
fibre products.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]

/-- Lemma 67.14.5: for closed subspaces `Z = subscheme I` and `Y = subscheme J` of an
algebraic space `X` over a scheme `S`, the scheme-theoretic intersection
`schemeTheoreticIntersection I J` includes into `Z` and into `Y` by closed immersions,
and the square with `subschemeι J` and `subschemeι I` is cartesian, i.e. it is the
fibre product `Z ×_X Y`. -/
@[stacks 0CZ0]
theorem schemeTheoreticIntersection_isPullback :
    IsPullback (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion (le_sup_left : I ≤ I ⊔ J)) (subschemeι J) (subschemeι I) :=
  sorry

#check
  (inferInstance :
    IsClosedImmersion (inclusion (le_sup_left : I ≤ I ⊔ J)))

#check
  (inferInstance :
    IsClosedImmersion (inclusion (le_sup_right : J ≤ I ⊔ J)))

end AlgebraicGeometry.AlgebraicSpace
