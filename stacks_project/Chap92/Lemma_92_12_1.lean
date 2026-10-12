/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.SymmetricPower
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Lemma 92.12.1: in the category-over-a-point setting of Example 21.39.1, if `C` has a
pointlike cosimplicial object as in Lemma 21.39.7 and `F` is a flat `B`-module-valued
presheaf with `moduleHomology F 0 = 0`, then the degree-`l` module-valued homology of
the degree-`k` symmetric power of `F` vanishes for all `l < k`. -/
@[stacks 08RD] #check
  (CategoryTheory.CategoryHomology.symmetricPower_isZero_of_lt :
    ∀ {C : Type u} [Category.{v} C] {B : Type w} [CommRing B]
      [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
      [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
      (Ubullet : CosimplicialObject C)
      (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
      (F : Cᵒᵖ ⥤ ModuleCat.{w} B)
      (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
      (h0 : IsZero (CategoryHomology.moduleHomology F 0))
      (k : ℕ) {l : ℕ} (h_lt : l < k),
      IsZero (CategoryHomology.moduleHomology
        (F ⋙ ModuleCat.symmetricPower.functor B k) l))

#check (CategoryTheory.CategoryHomology.symmetricPower_isZero_of_exists_pointlike :
  ∀ {C : Type u} [Category.{v} C] {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B)
    (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (CategoryHomology.moduleHomology F 0))
    (k : ℕ) {l : ℕ} (h_lt : l < k),
    IsZero (CategoryHomology.moduleHomology
      (F ⋙ ModuleCat.symmetricPower.functor B k) l))
