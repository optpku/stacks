/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations.Realization

/-!
# First-Page Comparisons for Alternative Cartan--Eilenberg Filtrations

This owner leaf contains the bounded and unbounded comparisons associated with the stupid
filtration and the first Cartan--Eilenberg spectral sequence.
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

namespace First

variable [HasInjectiveResolutions A]

/-- A comparison from a stupid-filtration realization to the first standard
Cartan--Eilenberg spectral sequence. -/
@[stacks 015X "first Cartan-Eilenberg spectral-sequence comparison"]
structure Comparison
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) where
  /-- The spectral-sequence realization produced by the stupid filtration. -/
  alternative : Stupid.Realization T Q K
  /-- The selected spectral sequence and concrete association data for the first standard
  Cartan--Eilenberg filtration. -/
  standard : FilteredComplex.AssociatedSpectralSequence
    (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex T))
  /-- The graded-piece comparisons for the selected first standard filtration. -/
  gradedPieceComparisons :
    HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex T)
  /-- The morphism from the alternative spectral sequence to the standard one. -/
  comparison : alternative.sequence ⟶ standard.sequence
  /-- The comparison commutes with the canonical first-page derived-functor identifications. -/
  pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
    CommSq
      ((comparison.hom 1).f (p, Int.ofNat q))
      (alternative.pageOneIso p q).hom
      (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
        I T standard.association gradedPieceComparisons p q).hom
      (𝟙 _)
  /-- The comparison is an isomorphism on every page from page one onward. -/
  isIsoFromPageOne : comparison.IsIsoFrom 1 zero_le_one

namespace Comparison

/-- Compute the first-page comparison map from the two derived-functor identifications. -/
@[stacks 015X "first-page comparison map computation"]
theorem pageOne_map_eq
    {T : A ⥤ B} [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {Q : HomotopyCategory.Plus A ⥤ E}
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : Comparison T Q K I) (p : ℤ) (q : ℕ) :
    (C.comparison.hom 1).f (p, Int.ofNat q) =
      (C.alternative.pageOneIso p q).hom ≫
        (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
          I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

/-- Inverse transport for the first-page comparison. -/
@[stacks 015X "inverse transport for the first-page comparison"]
theorem pageOne_inv_naturality
    {T : A ⥤ B} [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {Q : HomotopyCategory.Plus A ⥤ E}
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : Comparison T Q K I) (p : ℤ) (q : ℕ) :
    (C.alternative.pageOneIso p q).inv ≫
        (C.comparison.hom 1).f (p, Int.ofNat q) =
      (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
        I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

end Comparison

/-- Lemma 13.26.15 (`015X`): the stupid-filtration spectral sequence has a comparison with the
first standard Cartan--Eilenberg spectral sequence that is an isomorphism from page one onward. -/
@[stacks 015X "comparison with the first Cartan-Eilenberg spectral sequence"]
theorem comparison
    (T : A ⥤ B) [T.Additive]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) :
    Nonempty (Comparison T Q K I) := sorry

/-- A comparison that explicitly ties the unbounded stupid-filtration realization to the first
standard Cartan--Eilenberg filtered total. -/
@[stacks 015X "unbounded stupid-filtration comparison"]
structure UnboundedComparison
    [HasDerivedCategory.{w} A]
    (T : A ⥤ B) [T.Additive] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) where
  /-- The spectral sequence produced from the stupid filtration of `K`. -/
  alternative :
    CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization T K.obj
  /-- The selected spectral sequence of the first standard Cartan--Eilenberg filtered total. -/
  standard : FilteredComplex.AssociatedSpectralSequence
    (HomologicalComplex₂.First.Filtration.total (I.mapBicomplex T))
  /-- The graded-piece comparisons for the first standard filtration. -/
  gradedPieceComparisons :
    HomologicalComplex₂.First.GradedPiece.Comparisons (I.mapBicomplex T)
  /-- The morphism from the stupid-filtration sequence to the first standard sequence. -/
  comparison : alternative.sequence ⟶ standard.sequence
  /-- The comparison commutes with the common first-page right-derived identifications. -/
  pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
    CommSq
      ((comparison.hom 1).f (p, Int.ofNat q))
      (alternative.pageOneIso p q).hom
      (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
        I T standard.association gradedPieceComparisons p q).hom
      (𝟙 _)
  /-- The comparison is an isomorphism from the first page onward. -/
  isIsoFromPageOne : comparison.IsIsoFrom 1 zero_le_one

namespace UnboundedComparison

/-- Compute the unbounded first-page comparison map from the two derived-functor identifications.
-/
@[stacks 015X "unbounded first-page comparison map computation"]
theorem pageOne_map_eq
    [HasDerivedCategory.{w} A]
    {T : A ⥤ B} [T.Additive] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : UnboundedComparison T K I) (p : ℤ) (q : ℕ) :
    (C.comparison.hom 1).f (p, Int.ofNat q) =
      (C.alternative.pageOneIso p q).hom ≫
        (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
          I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

/-- Inverse transport for the unbounded first-page comparison. -/
@[stacks 015X "unbounded inverse transport for the first-page comparison"]
theorem pageOne_inv_naturality
    [HasDerivedCategory.{w} A]
    {T : A ⥤ B} [T.Additive] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : UnboundedComparison T K I) (p : ℤ) (q : ℕ) :
    (C.alternative.pageOneIso p q).inv ≫
        (C.comparison.hom 1).f (p, Int.ofNat q) =
      (CochainComplex.CartanEilenbergResolution.First.Association.pageOneIso
        I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

end UnboundedComparison

/-- The unbounded stupid-filtration sequence admits a comparison with the first standard
Cartan--Eilenberg sequence that is an isomorphism from `E₁` onward. -/
@[stacks 015X "unbounded comparison with the first Cartan-Eilenberg spectral sequence"]
theorem unboundedComparison
    [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{w} A]
    (T : A ⥤ B) [T.Additive] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) :
    Nonempty (UnboundedComparison T K I) := sorry

end First

end CochainComplex.CartanEilenbergResolution.SpectralSequence
