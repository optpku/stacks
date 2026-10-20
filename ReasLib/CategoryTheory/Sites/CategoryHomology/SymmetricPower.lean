module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]

/-- If a category has a pointlike cosimplicial object, the homology of a symmetric
power of a flat module-valued presheaf vanishes below the symmetric-power degree
when its degree-zero homology vanishes. -/
theorem symmetricPower_isZero_of_lt
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) {l : ℕ} (h_lt : l < k) :
    IsZero (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) l) := sorry

/-- If a pointlike cosimplicial object exists, the homology of a symmetric power
of a flat module-valued presheaf vanishes below the symmetric-power degree
when its degree-zero homology vanishes. -/
theorem symmetricPower_isZero_of_exists_pointlike
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) {l : ℕ} (h_lt : l < k) :
    IsZero (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) l) := sorry

/-- If a category has a pointlike cosimplicial object, the degree-`k` homology
of the `k`th symmetric power of a flat module-valued presheaf with zero
degree-zero homology is isomorphic to the `k`th exterior power of its first
homology. -/
theorem symmetricPower_isIsomorphic_exteriorPower
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) :
    IsIsomorphic (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((moduleHomology F 1).exteriorPower k) := sorry

/-- If a pointlike cosimplicial object exists, the degree-`k` homology of the
`k`th symmetric power of a flat module-valued presheaf with zero degree-zero
homology is isomorphic to the `k`th exterior power of its first homology. -/
theorem symmetricPower_isIsomorphic_exteriorPower_of_exists_pointlike
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) :
    IsIsomorphic (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) k)
      ((moduleHomology F 1).exteriorPower k) := sorry

end CategoryTheory.CategoryHomology
