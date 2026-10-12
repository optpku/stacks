/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre-product criteria for relative representability

Absolute reformulations of slice base change and transport of representability under changes of
the two cospan legs.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.TwoFibreProduct

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- A relative slice base change and the corresponding absolute two-fibre product carry the same
representability information. -/
@[stacks 02Y7 "slice base change versus absolute two-fibre product"]
theorem baseChange.isRepresentable_iff_apex
    {X Y : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) {U : C}
    (G : slice U ⟶ Y) :
    (FiberedCategoryOver.Groupoids.baseChange F G).IsRepresentable ↔
      IsRepresentable (G ⊡₂ F) := sorry
/- Proof strategy: apply `absolutize_isRepresentable_iff` to `baseChange F G` and transport its
absolute projection across the canonical equivalence with the two-fibre-product apex. -/

/-- A morphism is relatively representable exactly when every absolute two-fibre product with a
slice morphism is representable. -/
@[stacks 02Y7 "absolute two-fibre-product criterion for relative representability"]
theorem relativelyRepresentable.iff_forall_twoFibreProduct
    {X Y : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) :
    relativelyRepresentable F ↔
      ∀ ⦃U : C⦄ (G : slice U ⟶ Y),
        IsRepresentable (G ⊡₂ F) := sorry
/- Proof strategy: unfold `relativelyRepresentable` and rewrite each defining base-change clause
    with `baseChange.isRepresentable_iff_apex`. -/

/-- A relatively representable morphism with representable codomain has representable domain.
This is the fibred-category analogue of
`CategoryTheory.Functor.relativelyRepresentable.domain_isRepresentable` for presheaves. -/
@[stacks 02Y7 "representable domain of a relatively representable morphism"]
theorem relativelyRepresentable.domain_isRepresentable
    {X Y : FiberedCategoryOver.Groupoids C} {F : X ⟶ Y}
    (hF : relativelyRepresentable F) (hY : Y.IsRepresentable) :
    X.IsRepresentable := sorry
/- Proof strategy: choose an equivalence from `Y` to a canonical slice, transport `F` across
that equivalence, apply `relativelyRepresentable.iff_forall_twoFibreProduct` to the identity
slice test, and use the graph equivalence to identify the resulting two-fibre product with `X`. -/

/-- Base-changing a representable category fibred in groupoids along a slice map remains
representable. -/
@[stacks 02Y7 "representable two-fibre product along a slice map"]
theorem _root_.CategoryTheory.TwoFibreProduct.IsRepresentable.ofOverMap
    [Limits.HasPullbacks C]
    {Q : FiberedCategoryOver.Groupoids C} {U W : C}
    (j : Q ⟶ slice U) (f : W ⟶ U)
    (hQ : Q.IsRepresentable) :
    IsRepresentable ((overMap f) ⊡₂ j) := sorry
/- Proof strategy: choose a slice presentation of `Q`, identify `j` with a slice map, and use the
ordinary pullback of the two representing arrows. -/

/-- A two-fibre product is representable when its left source is representable and its right leg
is relatively representable. -/
@[stacks 02Y7 "representability from the left source and the right leg"]
theorem _root_.CategoryTheory.TwoFibreProduct.IsRepresentable.ofLeftSource
    {A B T : FiberedCategoryOver.Groupoids C}
    (F : A ⟶ T) {G : B ⟶ T}
    (hA : A.IsRepresentable) (hG : relativelyRepresentable G) :
    IsRepresentable (F ⊡₂ G) := sorry
/- Proof strategy: `relativelyRepresentable.homProperty.twoFibreProduct_fst F G hG` makes the first
projection relatively representable; apply
`relativelyRepresentable.domain_isRepresentable` with codomain `A`. -/

/-- A two-fibre product is representable when its right source is representable and its left leg
is relatively representable. -/
@[stacks 02Y7 "representability from the right source and the left leg"]
theorem _root_.CategoryTheory.TwoFibreProduct.IsRepresentable.ofRightSource
    {A B T : FiberedCategoryOver.Groupoids C}
    {F : A ⟶ T} (G : B ⟶ T)
    (hB : B.IsRepresentable) (hF : relativelyRepresentable F) :
    IsRepresentable (F ⊡₂ G) := sorry
/- Proof strategy: use `relativelyRepresentable.homProperty.twoFibreProduct_snd F G hF`, then apply
`relativelyRepresentable.domain_isRepresentable` with codomain `B`. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
