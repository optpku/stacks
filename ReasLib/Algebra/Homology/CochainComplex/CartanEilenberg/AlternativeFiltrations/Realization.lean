module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.FilteredDerivedTotal
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AssociatedDerivedPages
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.SpectralSequence
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation
public import ReasLib.CategoryTheory.Functor.Derived.SpectralSequence
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FromPage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Alternative Filtration Realizations for Cartan--Eilenberg Spectral Sequences

This owner leaf contains the chosen stupid-filtration and canonical-truncation realizations.
Their comparison objects are organized in the sibling `First` and `Second` leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]

namespace Stupid

variable [HasInjectiveResolutions A]

/-- A chosen stupid-filtration realization. Its first page consists of the right derived
functors of the terms of the bounded-below source complex. The comparison from a filtration
stage to brutal truncation is owned independently by `CochainComplex.StupidFiltration`. -/
@[stacks 015X "stupid-filtration spectral-sequence realization"]
structure Realization
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A)
    extends toDerivedRealization :
      CategoryTheory.Functor.RightDerived.SpectralSequence.Realization T Q K where
  /-- The first-page entry computes the right derived functor of the source term. -/
  pageOneIso : ∀ (p : ℤ) (q : ℕ),
    (sequence.page 1).X (p, Int.ofNat q) ≅ (T.rightDerived q).obj (K.obj.X p)
  /-- The first-page comparison identifies the differential with the derived source
  differential. -/
  pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
    CommSq
      ((sequence.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
      (pageOneIso p q).hom
      (pageOneIso (p + 1) q).hom
      ((T.rightDerived q).map (K.obj.d p (p + 1)))

/-- Lemma 13.26.15 (`015X`): the stupid filtration admits a chosen realization with its
derived-functor first-page formula. -/
@[stacks 015X "stupid-filtration construction"]
theorem nonempty
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) : Nonempty (Realization T Q K) := sorry

end Stupid

namespace Truncation

variable [HasInjectiveResolutions A]

/-- A chosen canonical-truncation realization. Its second page consists of the right derived
functors of the homology objects of the bounded-below source complex. The comparison between a
filtration stage and the canonical truncation is owned independently by
`CochainComplex.TruncationFiltration`. -/
@[stacks 015X "truncation-filtration spectral-sequence realization"]
structure Realization
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A)
    extends toDerivedRealization :
      CategoryTheory.Functor.RightDerived.SpectralSequence.Realization T Q K where
  /-- The second-page entry computes the right derived functor of the source homology object. -/
  pageTwoIso : ∀ (p : ℕ) (q : ℤ),
    (sequence.page 2).X (Int.ofNat p, q) ≅ (T.rightDerived p).obj (K.obj.homology q)

/-- Lemma 13.26.15 (`015X`): the canonical truncation filtration admits a chosen realization
with its derived-functor second-page formula. -/
@[stacks 015X "truncation-filtration construction"]
theorem nonempty
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) : Nonempty (Realization T Q K) := sorry

end Truncation

end CochainComplex.CartanEilenbergResolution.SpectralSequence
