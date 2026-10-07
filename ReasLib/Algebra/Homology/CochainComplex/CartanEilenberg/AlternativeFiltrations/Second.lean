module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations.Realization

/-!
# Second-Page Comparisons for Alternative Cartan--Eilenberg Filtrations

This owner leaf contains the bounded and renumbered comparisons associated with the canonical
truncation filtration and the second Cartan--Eilenberg spectral sequence.
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

namespace Second

variable [HasInjectiveResolutions A]

/-- A comparison from a canonical-truncation realization to the second standard
Cartan--Eilenberg spectral sequence. -/
@[stacks 015X "second Cartan-Eilenberg spectral-sequence comparison"]
structure Comparison
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) where
  /-- The spectral-sequence realization produced by the canonical truncation filtration. -/
  alternative : Truncation.Realization T Q K
  /-- The selected spectral sequence and concrete association data for the second standard
  Cartan--Eilenberg filtration. -/
  standard : FilteredComplex.AssociatedSpectralSequence
    (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex T))
  /-- The graded-piece comparisons for the selected second standard filtration. -/
  gradedPieceComparisons :
    HomologicalComplex₂.Second.GradedPiece.Comparisons (I.mapBicomplex T)
  /-- The morphism from the alternative spectral sequence to the standard one. -/
  comparison : alternative.sequence ⟶ standard.sequence
  /-- The comparison commutes with the canonical second-page derived-functor identifications. -/
  pageTwoCommSq : ∀ (p : ℕ) (q : ℤ),
    CommSq
      ((comparison.hom 2).f (Int.ofNat p, q))
      (alternative.pageTwoIso p q).hom
      (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
        I T standard.association gradedPieceComparisons p q).hom
      (𝟙 _)
  /-- The comparison is an isomorphism on every page from page one onward. -/
  isIsoFromPageOne : comparison.IsIsoFrom 1 zero_le_one

namespace Comparison

/-- Compute the second-page comparison map from the two derived-functor identifications. -/
@[stacks 015X "second-page comparison map computation"]
theorem pageTwo_map_eq
    {T : A ⥤ B} [T.Additive] [PreservesFiniteLimits T]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {Q : HomotopyCategory.Plus A ⥤ E}
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : Comparison T Q K I) (p : ℕ) (q : ℤ) :
    (C.comparison.hom 2).f (Int.ofNat p, q) =
      (C.alternative.pageTwoIso p q).hom ≫
        (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
          I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

/-- Inverse transport for the second-page comparison. -/
@[stacks 015X "inverse transport for the second-page comparison"]
theorem pageTwo_inv_naturality
    {T : A ⥤ B} [T.Additive] [PreservesFiniteLimits T]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {Q : HomotopyCategory.Plus A ⥤ E}
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : Comparison T Q K I) (p : ℕ) (q : ℤ) :
    (C.alternative.pageTwoIso p q).inv ≫
        (C.comparison.hom 2).f (Int.ofNat p, q) =
      (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
        I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

end Comparison

/-- Lemma 13.26.15 (`015X`): the canonical-truncation spectral sequence has a comparison with
the second standard Cartan--Eilenberg spectral sequence that is an isomorphism from page one
onward. -/
@[stacks 015X "comparison with the second Cartan-Eilenberg spectral sequence"]
theorem comparison
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [T.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) :
    Nonempty (Comparison T Q K I) := sorry

/-- A comparison that explicitly ties the renumbered truncation-filtration realization to the
second standard Cartan--Eilenberg filtered total. -/
@[stacks 015X "renumbered truncation-filtration comparison", stacks 0BKM]
structure RenumberedComparison
    [HasDerivedCategory.{w} A]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) where
  /-- The renumbered sequence produced from the truncation filtration of the localized source. -/
  alternative :
    CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization T
      ((DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).obj K.obj)
  /-- The selected spectral sequence of the second standard Cartan--Eilenberg filtered total. -/
  standard : FilteredComplex.AssociatedSpectralSequence
    (HomologicalComplex₂.Second.Filtration.total (I.mapBicomplex T))
  /-- The graded-piece comparisons for the second standard filtration. -/
  gradedPieceComparisons :
    HomologicalComplex₂.Second.GradedPiece.Comparisons (I.mapBicomplex T)
  /-- The localization identifies derived-category cohomology with cochain-complex cohomology. -/
  homologyIso : ∀ q : ℤ,
    (DerivedCategory.homologyFunctor A q).obj
        ((DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).obj K.obj) ≅
      K.obj.homology q
  /-- The morphism from the renumbered truncation sequence to the second standard sequence,
  regarded as beginning at `E₂`. -/
  comparison : alternative.sequence ⟶
    SpectralSequence.Page.Two.ofZero standard.sequence
  /-- The comparison commutes with the common second-page right-derived identifications. -/
  pageTwoCommSq : ∀ (p : ℕ) (q : ℤ),
    CommSq
      ((comparison.hom 2).f (Int.ofNat p, q))
      (alternative.pageTwoIso p q).hom
      (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
        I T standard.association gradedPieceComparisons p q).hom
      ((T.rightDerived p).map (homologyIso q).hom)
  /-- The comparison is an isomorphism from the second page onward. -/
  isIsoFromPageTwo : comparison.IsIsoFrom 2 le_rfl

namespace RenumberedComparison

/-- Compute the renumbered second-page comparison map from the two page identifications. -/
@[stacks 015X "renumbered second-page comparison map computation", stacks 0BKM]
theorem pageTwo_map_eq
    [HasDerivedCategory.{w} A]
    {T : A ⥤ B} [T.Additive] [PreservesFiniteLimits T] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : RenumberedComparison T K I) (p : ℕ) (q : ℤ) :
    (C.comparison.hom 2).f (Int.ofNat p, q) =
      (C.alternative.pageTwoIso p q).hom ≫
        (T.rightDerived p).map (C.homologyIso q).hom ≫
        (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
          I T C.standard.association C.gradedPieceComparisons p q).inv := sorry

/-- Inverse transport for the renumbered second-page comparison. -/
@[stacks 015X "renumbered inverse transport for the second-page comparison", stacks 0BKM]
theorem pageTwo_inv_naturality
    [HasDerivedCategory.{w} A]
    {T : A ⥤ B} [T.Additive] [PreservesFiniteLimits T] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    {K : CochainComplex.Plus A} {I : CartanEilenbergResolution K}
    (C : RenumberedComparison T K I) (p : ℕ) (q : ℤ) :
    (T.rightDerived p).map (C.homologyIso q).hom ≫
        (CochainComplex.CartanEilenbergResolution.Second.Association.pageTwoIso
          I T C.standard.association C.gradedPieceComparisons p q).inv =
      (C.alternative.pageTwoIso p q).inv ≫
        (C.comparison.hom 2).f (Int.ofNat p, q) := sorry

end RenumberedComparison

/-- The renumbered truncation-filtration sequence admits a comparison with the second standard
Cartan--Eilenberg sequence that is an isomorphism from `E₂` onward. -/
@[stacks 015X "renumbered comparison with the second Cartan-Eilenberg spectral sequence",
  stacks 0BKM]
theorem renumberedComparison
    [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{w} A]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [T.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived T]
    (K : CochainComplex.Plus A) (I : CartanEilenbergResolution K) :
    Nonempty (RenumberedComparison T K I) := sorry

end Second

end CochainComplex.CartanEilenbergResolution.SpectralSequence
