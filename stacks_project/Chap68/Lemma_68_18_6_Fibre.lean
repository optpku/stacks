/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

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
  sorry

/-- The canonical morphism `|X_k| ⟶ |X|` from the field-valued fibre of `f` at `p`. -/
def fieldFiberι : fieldFiber f p ⟶ X :=
  pullback.fst f p.hom

/-- `fieldFiberι f p` is the first projection of the fibre product `X ×_Y Spec(k)`. -/
theorem fieldFiberι_eq : fieldFiberι f p = pullback.fst f p.hom :=
  sorry

/-- The structure morphism of the field-valued fibre of `f` at `p` to `Spec(k)`. -/
def fieldFiberToSpec : fieldFiber f p ⟶ ofOver p.overObj :=
  pullback.snd f p.hom

/-- `fieldFiberToSpec f p` is the second projection of the fibre product
`X ×_Y Spec(k)`. -/
theorem fieldFiberToSpec_eq : fieldFiberToSpec f p = pullback.snd f p.hom :=
  sorry

/-- The field-valued fibre of `f` at `p` is the cartesian square of `f` against
`p.hom`. -/
theorem fieldFiber_isPullback :
    IsPullback (fieldFiberι f p) (fieldFiberToSpec f p) f p.hom :=
  sorry

/-- The two projections of the field-valued fibre satisfy the pullback condition. -/
theorem fieldFiberι_comp :
    fieldFiberι f p ≫ f = fieldFiberToSpec f p ≫ p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
