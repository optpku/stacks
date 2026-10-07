module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation

/-!
# Vanishing of homology of symmetric powers

On a category over a point, category homology of symmetric powers of a flat
`underline{B}`-module vanishes strictly below the symmetric-power degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]

/-- Category homology of a `B`-module-valued presheaf, as the left-derived colimit.
This is the module-coefficient parallel of `categoryHomology`, corresponding to
`H_n(C, -) = L_n π_!` for the chaotic topology with `𝒪 = underline{B}`. -/
abbrev moduleHomology {B : Type w} [Ring B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (n : ℕ) : ModuleCat.{w} B :=
  ((colim : (Cᵒᵖ ⥤ ModuleCat.{w} B) ⥤ ModuleCat.{w} B).leftDerived n).obj F

/-- Lemma 92.12.1: in the category-over-a-point setting of Example 21.39.1, if `C` has a
pointlike cosimplicial object as in Lemma 21.39.7 and `F` is a flat `underline{B}`-module
with `H_0(C, F) = 0`, then `H_l(C, Sym_underline{B}^k(F)) = 0` for all `l < k`. -/
@[stacks 08RD]
theorem symmetricPower_isZero_of_lt
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) {l : ℕ} (h_lt : l < k) :
    IsZero (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) l) := sorry

/-- If a pointlike cosimplicial object exists, the same vanishing holds for homology of
symmetric powers of a flat `B`-module-valued presheaf with vanishing `H_0`. -/
theorem symmetricPower_isZero_of_exists_pointlike
    {B : Type w} [CommRing B]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{w} B)]
    [HasProjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{w} B)]
    (hUbullet : ∃ Ubullet : CosimplicialObject C,
      CosimplicialObject.Pointlike.HasHomSpaces Ubullet)
    (F : Cᵒᵖ ⥤ ModuleCat.{w} B) (h_flat : ∀ X : Cᵒᵖ, Module.Flat B (F.obj X))
    (h0 : IsZero (moduleHomology F 0)) (k : ℕ) {l : ℕ} (h_lt : l < k) :
    IsZero (moduleHomology (F ⋙ ModuleCat.symmetricPower.functor B k) l) := sorry

end CategoryTheory.CategoryHomology
