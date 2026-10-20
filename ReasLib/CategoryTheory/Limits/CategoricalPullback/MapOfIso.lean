module

import Mathlib.Tactic.CrossRefAttribute
-- `MapProperties` exports the generic categorical-pullback map and its property-transfer
-- instances; this specialization needs neither an explicit quasi-inverse nor any endpoint
-- transport API.
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.MapProperties

/-!
# Properties of categorical-pullback maps induced by invertible squares

Faithfulness, fullness, and equivalence specializations for the pullback map induced by
`CatCospanTransform.ofIso`.
-/

@[expose] public section

namespace CategoryTheory.Limits.CatCospanTransform.OfIso

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}
variable (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/- These instances retain the explicit comparison cells and specialize the reusable transfer
instances to `CatCospanTransform.ofIso β α.symm`. They live below the constructor that determines
their hypotheses, rather than introducing a second name for the induced functor or a bundled
non-`Prop` fully-faithful witness. -/

/-- If `K` and `L` are faithful, then the categorical-pullback map induced by
`CatCospanTransform.ofIso β α.symm` is faithful. -/
@[stacks 02XB "faithfulness of the induced 2-fibre-product functor"]
instance mapFaithful [K.Faithful] [L.Faithful] :
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).Faithful := sorry
/- Proof strategy: this is `CategoricalPullback.map.faithful` specialized to
`CatCospanTransform.ofIso β α.symm`, whose side functors are definitionally `L` and `K`. -/

/-- If `K` and `L` are full and `M` is faithful, then the categorical-pullback map induced by
`CatCospanTransform.ofIso β α.symm` is full. It is intentionally atomic so typeclass search can
compose it with `mapFaithful` without constructing a bundled fully-faithful witness. -/
@[stacks 02XB "full faithfulness of the induced 2-fibre-product functor"]
instance mapFull [K.Full] [L.Full] [M.Faithful] :
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).Full := sorry
/- Proof strategy: specialize `CategoricalPullback.map.full` to
`CatCospanTransform.ofIso β α.symm`, whose side and base functors are definitionally `L`,
`K`, and `M`. This named specialization bridges the opacity of `ofIso` across module boundaries. -/

/-- If `K` and `L` are equivalences and
`M` is fully faithful, then
`CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)` is an equivalence. -/
@[stacks 02XB "equivalence of the induced 2-fibre-product functor"]
instance mapIsEquivalence
    [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] :
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).IsEquivalence := sorry
/- Proof strategy: specialize `CategoricalPullback.map.isEquivalence` to
`CatCospanTransform.ofIso β α.symm`; its three component functors are `L`, `M`, and `K`. -/

end CategoryTheory.Limits.CatCospanTransform.OfIso
