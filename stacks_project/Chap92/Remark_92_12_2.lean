/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.SymmetricPower
import StacksCheckRecall

/-!
# Diagonal homology of symmetric powers

In the situation of Lemma 92.12.1, the degree-`k` homology of the `k`th
symmetric power of a flat `underline{B}`-module is identified with the `k`th
exterior power of first homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]

/- Remark 92.12.2: in the situation of Lemma 92.12.1, if `C` has a pointlike
cosimplicial object and `F` is a flat `underline{B}`-module with
`H_0(C, F) = 0`, then `H_k(C, Sym^k(F))` is isomorphic to
`∧^k_B(H_1(C, F))`. Equivalently,
`moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) k` is
`IsIsomorphic` to `(moduleHomology F 1).exteriorPower k`. This is the
`S_k`-coinvariants of
`H^{-k}(Lπ!(F) ⊗_B^L ⋯ ⊗_B^L Lπ!(F)) = H_1(C, F)^{⊗ k}`, where the
`S_k`-action is the usual tensor permutation action multiplied by
`Equiv.Perm.sign`; the sign conventions of the total complex of a
multicomplex are omitted. -/
@[stacks 08SG] #check
  (CategoryTheory.CategoryHomology.symmetricPower_isIsomorphic_exteriorPower :
    ∀ {C : Type u} [Category.{v} C]
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ),
    IsIsomorphic (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((moduleHomology F 1).exteriorPower k))

/- If a pointlike cosimplicial object exists, the same identification holds
between diagonal homology of symmetric powers and the exterior power of first
homology. -/
#check
  (CategoryTheory.CategoryHomology.symmetricPower_isIsomorphic_exteriorPower_of_exists_pointlike :
    ∀ {C : Type u} [Category.{v} C]
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ),
    IsIsomorphic (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((moduleHomology F 1).exteriorPower k))

end CategoryTheory.CategoryHomology
