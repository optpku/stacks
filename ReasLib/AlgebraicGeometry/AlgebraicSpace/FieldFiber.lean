/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-!
# Field-valued fibres of morphisms of algebraic spaces

The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a field-valued
point `p` of `Y` is the fibre product `X ×_Y Spec(k)`, with projections to `X`
and to `Spec(k)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y)

/-- The fibre of `f` over a field-valued point `p`, as the fibre product
`X ×_Y Spec(k)`. -/
def fieldFiber : AlgebraicSpace S :=
  pullback f p.hom

/-- `fieldFiber f p` is the chosen fibre product of `f` with `p.hom`. -/
theorem fieldFiber_eq : fieldFiber f p = pullback f p.hom :=
  rfl

/-- The canonical morphism from the field-valued fibre of `f` at `p` to `X`. -/
def fieldFiberι : fieldFiber f p ⟶ X :=
  pullback.fst f p.hom

/-- `fieldFiberι f p` is the first projection of the fibre product `X ×_Y Spec(k)`. -/
theorem fieldFiberι_eq : fieldFiberι f p = pullback.fst f p.hom :=
  rfl

/-- The structure morphism of the field-valued fibre of `f` at `p` to `Spec(k)`. -/
def fieldFiberToSpec : fieldFiber f p ⟶ ofOver p.overObj :=
  pullback.snd f p.hom

/-- `fieldFiberToSpec f p` is the second projection of the fibre product
`X ×_Y Spec(k)`. -/
theorem fieldFiberToSpec_eq : fieldFiberToSpec f p = pullback.snd f p.hom :=
  rfl

/-- The field-valued fibre of `f` at `p` is the cartesian square of `f` against
`p.hom`. -/
theorem fieldFiber_isPullback :
    IsPullback (fieldFiberι f p) (fieldFiberToSpec f p) f p.hom :=
  IsPullback.of_hasPullback f p.hom

/-- The two projections of the field-valued fibre satisfy the pullback condition. -/
theorem fieldFiberι_comp :
    fieldFiberι f p ≫ f = fieldFiberToSpec f p ≫ p.hom :=
  pullback.condition

/-- The scheme-theoretic fibre of `f` over a field-valued point `p`, viewed as an algebraic
space over `Spec (.of p.K)` by reindexing along `fieldFiberToSpec f p`. -/
def fiberOverField : AlgebraicSpace (Spec (.of p.K)) :=
  restrictOver (Over.mk (fieldFiberToSpec f p))

/-- The fibre over its representative field is the restriction of its canonical
structure morphism to that field. -/
theorem fiberOverField_eq :
    fiberOverField f p = restrictOver (Over.mk (fieldFiberToSpec f p)) :=
  rfl

/-- If `p₀.hom` is a monomorphism representing `f(x)`, there is a unique point of
the fibre mapping to `x`. -/
theorem existsUnique_fieldFiber_point_of_mono {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x) :
    ∃! t : Points (fieldFiber f p₀), Points.map (fieldFiberι f p₀) t = x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
