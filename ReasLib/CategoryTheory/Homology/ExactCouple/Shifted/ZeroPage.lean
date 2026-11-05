/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Shifted
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeroth Pages for Shifted Exact Couples

This module adjoins a specified zeroth page to the positive-page spectral sequence of a shifted
exact couple. It is a bridge for constructions where the first page is identified with the
homology of a shifted differential object; construction of the exact couple itself remains a
separate concern.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ShiftedExactCouple.ZeroPage

section ZeroPage

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : C ≌ C}

variable (X : ShiftedExactCouple (S.trans T) T)
variable (Q : ShiftedDifferentialObject S.functor)

/-- The zero-based page family obtained by adjoining `Q.previousPage`, with shift `S`, to the
positive pages of an exact couple with initial shift `T ∘ S`. -/
@[stacks 0AMK]
def page (r : ℕ) : ShiftedDifferentialObject ((ShiftedSpectralSequence.zeroPageShift S T r).functor) :=
  match r with
  | 0 => Q.previousPage
  | r + 1 => (Derived.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩

/-- The zeroth page is `Q.previousPage`. -/
@[simp]
theorem page_zero : page X Q 0 = Q.previousPage := rfl

/-- Positive pages agree with the associated shifted spectral sequence. -/
@[simp]
theorem page_succ (r : ℕ) :
    page X Q (r + 1) = (Derived.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩ := rfl

/-- The object on the zeroth page is the previous-page object. -/
@[simp]
theorem page_zero_obj : (page X Q 0).obj = Q.previousPage.obj := rfl

/-- The zeroth differential is the previous-page differential. -/
@[simp]
theorem page_zero_d : (page X Q 0).d = Q.previousPage.d := rfl

/-- The object on page `r + 1` is the page object of the `r`-fold derived exact couple. -/
theorem page_succ_obj (r : ℕ) :
    (page X Q (r + 1)).obj = (Derived.iterate X r).E := rfl

/-- The differential on page `r + 1` is induced by the `r`-fold derived exact couple. -/
theorem page_succ_d (r : ℕ) :
    (page X Q (r + 1)).d = (Derived.iterate X r).d := rfl

/-- The first positive page is the page object of the original exact couple. -/
@[simp]
theorem page_one_obj : (page X Q 1).obj = X.E := rfl

/-- The first positive differential is the differential of the original exact couple. -/
@[simp]
theorem page_one_d : (page X Q 1).d = X.d := rfl

/-- The identification of the initial exact-couple page object with the inverse shift of
`Q.homology`.  The zero-based page family supplies the source-facing page-one bridge separately. -/
@[stacks 0AMK "(6)"]
abbrev homologyIso (e : X.E ≅ Q.previousPage.homology) :
    X.E ≅ S.functor.inv.obj Q.homology :=
  e ≪≫ ShiftedDifferentialObject.PreviousPage.homologyIso Q

/-- The zero-based cycle filtration pulled back from the associated shifted spectral sequence. -/
@[stacks 0AMK]
noncomputable abbrev cycle (e : X.E ≅ Q.previousPage.homology) : ℕ → Subobject Q.previousPage.obj :=
  (Derived.associatedSpectralSequence X).homologyPageTower.preimageCycle Q.previousPage.shortComplex e

/-- The zero-based boundary filtration pulled back from the associated shifted spectral sequence. -/
@[stacks 0AMK]
noncomputable abbrev boundary (e : X.E ≅ Q.previousPage.homology) : ℕ → Subobject Q.previousPage.obj :=
  (Derived.associatedSpectralSequence X).homologyPageTower.preimageBoundary Q.previousPage.shortComplex e

/-- The positive cycle stages are the pullbacks of the owner cycle stages. -/
@[simp]
theorem cycle_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    cycle X Q e (r + 1) =
      ShortComplex.Cycles.preimageOfIso Q.previousPage.shortComplex e
        ((Derived.associatedSpectralSequence X).cycle ⟨r + 1, Nat.succ_pos _⟩) := rfl

/-- The positive boundary stages are the pullbacks of the owner boundary stages. -/
@[simp]
theorem boundary_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    boundary X Q e (r + 1) =
      ShortComplex.Cycles.preimageOfIso Q.previousPage.shortComplex e
        ((Derived.associatedSpectralSequence X).boundary ⟨r + 1, Nat.succ_pos _⟩) := rfl

/-- The zeroth cycle stage is the whole zeroth-page object. -/
@[simp]
theorem cycle_zero (e : X.E ≅ Q.previousPage.homology) : cycle X Q e 0 = ⊤ := rfl

/-- The zeroth boundary stage is zero. -/
@[simp]
theorem boundary_zero (e : X.E ≅ Q.previousPage.homology) : boundary X Q e 0 = ⊥ := rfl

end ZeroPage

end ShiftedExactCouple.ZeroPage
end CategoryTheory
