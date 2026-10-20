module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 32.2.2

The directed affine-transition limit infrastructure is maintained by
Mathlib's `AffineTransitionLimit` API and the neutral existence bridge in
`ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (c : Cone D) (hc : IsLimit c)
variable (i0 : OrderDual I) (U0 : (D.obj i0).Opens)

/- Lemma 32.2.2: A directed inverse diagram of schemes with affine transition
morphisms admits a limit cone. -/
@[stacks 01YX] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.nonemptyCone D :
    Nonempty (LimitCone D))

/- Every projection from a limiting cone of a cofiltered diagram with affine
transition morphisms is affine. -/
#check
  (AlgebraicGeometry.isAffineHom_π_app D c hc :
    ∀ i : OrderDual I, IsAffineHom (c.π.app i))

/- The inverse image of an open at one stage is the limit of the corresponding
tail diagram of inverse-image opens. -/
#check
  (AlgebraicGeometry.isLimitOpensCone D c hc i0 U0 :
    IsLimit (AlgebraicGeometry.opensCone D c i0 U0))
