/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap109.Lemma_109_9_1_Substack
public import stacks_project.Chap109.Lemma_109_9_3_HigherDirectImage

/-!
# The object property of families of curves of a given genus

`𝒞urves_g` is the full subcategory of families of curves in `𝒞urves^{h0, 1}`
for which `R^1 f_* 𝒪_X` is finite locally free of rank `g`. Membership is the
source-facing packaging of a classifying morphism factoring through that
open-and-closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X`, fibres of dimension `1`, and `R^1 f_* 𝒪_X` finite locally
free of rank `g`, corresponding to the open-and-closed substack `𝒞urves_g`. -/
def ofGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    h0Dim1 S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `ofGenus g` means the unit `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after every base change, including the identity, every fibre has dimension `1`,
and `R^1 f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem ofGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    ofGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        (∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)) :=
  sorry

/-- The `ofGenus` property of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_ofGenus (g : ℕ) (S : Scheme.{u}) :
    (ofGenus g S).IsClosedUnderIsomorphisms :=
  sorry

/-- Membership in `ofGenus g` implies membership in `h0Dim1`. -/
theorem ofGenus_le_h0Dim1 (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    ofGenus g S P → h0Dim1 S P :=
  sorry

/-- A family of curves lies in at most one of the substacks `𝒞urves_g`. -/
theorem eq_of_mem_ofGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : ofGenus g S P) (hg' : ofGenus g' S P) : g = g' :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
