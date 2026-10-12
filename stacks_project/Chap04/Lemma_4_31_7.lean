/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.MapOfIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

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

/- Lemma 4.31.7 (1): faithful side functors induce a faithful functor on the corresponding
`2`-fibre products. -/
@[stacks 02XB "faithfulness of the induced 2-fibre-product functor"]
#check (fun [K.Faithful] [L.Faithful] ↦
  CategoryTheory.Limits.CatCospanTransform.OfIso.mapFaithful α β :
  ∀ [K.Faithful] [L.Faithful],
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).Faithful)

/- Lemma 4.31.7 (2): fully faithful side functors, with faithful base functor, induce a fully
faithful functor on `2`-fibre products. -/
@[stacks 02XB "full faithfulness of the induced 2-fibre-product functor"]
#check (fun [K.Full] [L.Full] [M.Faithful] ↦
  CategoryTheory.Limits.CatCospanTransform.OfIso.mapFull α β :
  ∀ [K.Full] [L.Full] [M.Faithful],
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).Full)

/- Lemma 4.31.7 (3): equivalences on the two sides, with fully faithful base functor, induce an
equivalence on `2`-fibre products. -/
@[stacks 02XB "equivalence of the induced 2-fibre-product functor"]
#check (fun [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful] ↦
  CategoryTheory.Limits.CatCospanTransform.OfIso.mapIsEquivalence α β :
  ∀ [K.IsEquivalence] [L.IsEquivalence] [M.Full] [M.Faithful],
    (CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)).IsEquivalence)
