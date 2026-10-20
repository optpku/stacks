/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import ReasLib.CategoryTheory.Homology.Homotopy.CochainShift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies Between Degreewise-Split Cochain Connecting Maps

Changing a degreewise splitting changes the associated cochain connecting morphism by a
homotopy whose components are the negatives of the section corrections.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace CochainComplex

open HomComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace DegreewiseSplit.Homotopy

/-- The degree `-1` cochain determined by the negatives of a family of section corrections. -/
def cochain (S : ShortComplex (CochainComplex C ℤ))
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁) :
    Cochain S.X₃ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
  Cochain.mk fun p q hpq ↦
    (-h p) ≫ (S.X₁.shiftFunctorObjXIso 1 q p ((sub_eq_iff_eq_add).mp hpq)).inv

/-- The coboundary of `cochain` is the difference between the connecting morphisms associated
to the corrected and original splittings. -/
theorem cochain_spec (S : ShortComplex (CochainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) :
    Cochain.ofHom (homOfDegreewiseSplit S σ') =
      δ (-1) 0 (cochain S h) + Cochain.ofHom (homOfDegreewiseSplit S σ) := sorry

/-- Correcting a degreewise splitting yields a homotopy from the corrected cochain connecting
morphism to the original one. -/
@[stacks 011L]
def ofCorrection (S : ShortComplex (CochainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) :
    Homotopy (homOfDegreewiseSplit S σ') (homOfDegreewiseSplit S σ) :=
  (Cochain.equivHomotopy (homOfDegreewiseSplit S σ')
      (homOfDegreewiseSplit S σ)).symm
    ⟨cochain S h, cochain_spec S σ σ' h hs⟩

/-- The degree-`n` component of `ofCorrection` is `-h n` under the standard shift
identification. -/
theorem component_comp_shiftIso (S : ShortComplex (CochainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) (n : ℤ) :
    (ofCorrection S σ σ' h hs).hom n (n - 1) ≫
        (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (sub_add_cancel n 1).symm).hom =
      -h n := sorry

end DegreewiseSplit.Homotopy

end


end CochainComplex
