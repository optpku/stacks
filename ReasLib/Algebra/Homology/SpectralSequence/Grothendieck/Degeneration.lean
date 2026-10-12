/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Degeneration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degeneration of Grothendieck spectral sequences

This file transports single-row and single-column degeneration from a neutral filtered
realization to the canonical page-two and abutment objects of a Grothendieck spectral sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]
variable (G : B ⥤ C) [G.Additive]
variable (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
variable (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
variable (X : DerivedCategory.Plus A)

namespace PageTwo

/-- The canonical Grothendieck second-page targets are concentrated in row `q`. -/
@[stacks 015N "Grothendieck second page concentrated in one row"]
def IsConcentratedInRow (q : ℤ) : Prop :=
  ∀ p : ℕ, ∀ q' : ℤ, q' ≠ q → IsZero (pageTwo G RF X p q')

/-- The canonical Grothendieck second-page targets are concentrated in column `p`. -/
@[stacks 015N "Grothendieck second page concentrated in one column"]
def IsConcentratedInColumn (p : ℕ) : Prop :=
  ∀ p' : ℕ, ∀ q : ℤ, p' ≠ p → IsZero (pageTwo G RF X p' q)

end PageTwo

namespace SpectralSequence

namespace Degeneration

/-- A Grothendieck spectral sequence concentrated in one row identifies its abutment with the
unique canonical page-two target in each total degree. -/
@[stacks 015N "single-row Grothendieck degeneration"]
theorem row (S : SpectralSequence G RF RGF X) {q : ℤ}
    (h : PageTwo.IsConcentratedInRow G RF X q) (p : ℕ) :
    IsIsomorphic (abutment RGF X (Int.ofNat p + q)) (pageTwo G RF X p q) := sorry

/-- A Grothendieck spectral sequence concentrated in one column identifies its abutment with
the unique canonical page-two target in each total degree. -/
@[stacks 015N "single-column Grothendieck degeneration"]
theorem column (S : SpectralSequence G RF RGF X) {p : ℕ}
    (h : PageTwo.IsConcentratedInColumn G RF X p) (q : ℤ) :
    IsIsomorphic (abutment RGF X (Int.ofNat p + q)) (pageTwo G RF X p q) := sorry

end Degeneration

end SpectralSequence

end CategoryTheory.Functor.RightDerived.Grothendieck
