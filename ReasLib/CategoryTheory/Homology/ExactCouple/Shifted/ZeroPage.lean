/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

variable (K : Derived.Construction T)
variable (X : ShiftedExactCouple S T)
variable (Q : ShiftedDifferentialObject S.functor)

/-- The zero-based page family obtained by adjoining `Q.previousPage` to the positive pages of
`K.associatedSpectralSequence X`. -/
@[stacks 0AMK]
def page (r : ℕ) : ShiftedDifferentialObject ((ShiftedSpectralSequence.zeroPageShift S T r).functor) :=
  match r with
  | 0 => Q.previousPage
  | r + 1 => (K.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩

/-- The zeroth page is `Q.previousPage`. -/
@[simp]
theorem page_zero : page K X Q 0 = Q.previousPage := sorry

/-- Positive pages agree with the associated shifted spectral sequence. -/
@[simp]
theorem page_succ (r : ℕ) :
    page K X Q (r + 1) = (K.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩ := sorry

/-- The object on the zeroth page is the previous-page object. -/
@[simp]
theorem page_zero_obj : (page K X Q 0).obj = Q.previousPage.obj := sorry

/-- The zeroth differential is the previous-page differential. -/
@[simp]
theorem page_zero_d : (page K X Q 0).d = Q.previousPage.d := sorry

/-- The object on page `r + 1` is the page object of the `r`-fold derived exact couple. -/
theorem page_succ_obj (r : ℕ) :
    (page K X Q (r + 1)).obj = (K.iterate X r).E := sorry

/-- The differential on page `r + 1` is induced by the `r`-fold derived exact couple. -/
theorem page_succ_d (r : ℕ) :
    (page K X Q (r + 1)).d = (K.iterate X r).d := sorry

/-- The first positive page is the page object of the original exact couple. -/
@[simp]
theorem page_one_obj : (page K X Q 1).obj = X.E := sorry

/-- The first positive differential is the differential of the original exact couple. -/
@[simp]
theorem page_one_d : (page K X Q 1).d = X.d := sorry

/-- The identification of the initial exact-couple page object with the inverse shift of
`Q.homology`.  The zero-based page family supplies the source-facing page-one bridge separately. -/
@[stacks 0AMK "(6)"]
abbrev homologyIso (e : X.E ≅ Q.previousPage.homology) :
    X.E ≅ S.functor.inv.obj Q.homology :=
  e ≪≫ ShiftedDifferentialObject.PreviousPage.homologyIso Q

/-- The zero-based cycle filtration pulled back from the associated shifted spectral sequence. -/
@[stacks 0AMK]
noncomputable abbrev cycle (e : X.E ≅ Q.previousPage.homology) : ℕ → Subobject Q.previousPage.obj :=
  (K.associatedSpectralSequence X).homologyPageTower.preimageCycle Q.previousPage.shortComplex e

/-- The zero-based boundary filtration pulled back from the associated shifted spectral sequence. -/
@[stacks 0AMK]
noncomputable abbrev boundary (e : X.E ≅ Q.previousPage.homology) : ℕ → Subobject Q.previousPage.obj :=
  (K.associatedSpectralSequence X).homologyPageTower.preimageBoundary Q.previousPage.shortComplex e

/-- The positive cycle stages are the pullbacks of the owner cycle stages. -/
@[simp]
theorem cycle_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    cycle K X Q e (r + 1) =
      ShortComplex.Cycles.preimageOfIso Q.previousPage.shortComplex e
        ((K.associatedSpectralSequence X).cycle ⟨r + 1, Nat.succ_pos _⟩) := sorry

/-- The positive boundary stages are the pullbacks of the owner boundary stages. -/
@[simp]
theorem boundary_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    boundary K X Q e (r + 1) =
      ShortComplex.Cycles.preimageOfIso Q.previousPage.shortComplex e
        ((K.associatedSpectralSequence X).boundary ⟨r + 1, Nat.succ_pos _⟩) := sorry

/-- The zeroth cycle stage is the whole zeroth-page object. -/
@[simp]
theorem cycle_zero (e : X.E ≅ Q.previousPage.homology) : cycle K X Q e 0 = ⊤ := sorry

/-- The zeroth boundary stage is zero. -/
@[simp]
theorem boundary_zero (e : X.E ≅ Q.previousPage.homology) : boundary K X Q e 0 = ⊥ := sorry

end ZeroPage

end ShiftedExactCouple.ZeroPage
end CategoryTheory
