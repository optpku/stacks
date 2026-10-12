/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Second-page support for truncation-filtration realizations

The nonnegative columns are identified with right-derived functors by `Realization.pageTwoIso`.
This leaf records the complementary negative-column vanishing statement on the actual
integer-indexed spectral-sequence surface.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- [stacks 0BKM] The second page of a truncation-filtration realization vanishes in negative
right-derived degree. -/
@[stacks 0BKM "negative-column vanishing on the truncation spectral sequence"]
theorem pageTwoIsZero
    {K : DerivedCategory A} (S : Realization F K) (i j : ℤ) (hi : i < 0) :
    Limits.IsZero ((S.sequence.page 2).X (i, j)) := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
