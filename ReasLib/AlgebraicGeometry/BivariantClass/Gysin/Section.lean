/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The degree-zero identity class of `𝟙 X`, obtained by conjugating `ChowCohomology.one` along
`overMkIso X`. -/
noncomputable def oneOver
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    BivariantClass δ (𝟙 X) 0 :=
  restrict δ (overMkIso X).inv (𝟙 X) (overMkIso X).inv
    (overMkIso_id_isPullback X) 0 (ChowCohomology.one δ X.hom)

/-- `oneOver` is restriction of `ChowCohomology.one` along the canonical `Over.mk` isomorphism. -/
theorem oneOver_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    oneOver δ X =
      restrict δ (overMkIso X).inv (𝟙 X) (overMkIso X).inv
        (overMkIso_id_isPullback X) 0
        (ChowCohomology.one δ X.hom) := sorry

/-- A section of a smooth morphism over a dimensioned base is a regular immersion. -/
theorem section_isRegularImmersion
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) :
    IsRegularImmersion s.left :=
  Scheme.Hom.Section.isRegularImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs)

/-- For a smooth morphism of constant relative dimension, the normal Gysin class of a
section composed with smooth flat pullback is the degree-zero identity class. -/
theorem gysin_section_comp_flatPullback_eq_one
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (r : ℕ) [Scheme.Hom.RelativeDimension p.left r]
    (s : X ⟶ P) [IsImmersion s.left] (hs : s ≫ p = 𝟙 X)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedDeformation X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder) :
    Nonnegative.castGrading δ (add_neg_cancel (r : ℤ))
        (hs ▸ comp δ s p (gysinSection δ s r e D) (flatPullback δ p r)) =
      oneOver δ X := sorry

/-- Capping the identity `s^! ∘ p^*` against the Chow class of an integral closed subscheme of
`X` recovers that class. -/
theorem gysin_section_comp_flatPullback_cap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (r : ℕ) [Scheme.Hom.RelativeDimension p.left r]
    (s : X ⟶ P) [IsImmersion s.left] (hs : s ≫ p = 𝟙 X)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf s.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf s.left) ≅
      Scheme.Hom.conormalSheaf s.left)
    (D : ClosedDeformation X.hom (s.left.coborderRange.ι ≫ P.hom)
      s.left.liftCoborder
      (factorization_over X.hom P.hom s.left s.w
        s.left.liftCoborder s.left.coborderRange.ι s.left.liftCoborder_ι)
      (ofNormalSheaf s.left r e).toCoborder)
    (Z : X.left.IdealSheafData) [IsIntegral Z.subscheme] (n : ℤ)
    (hZ : X.hom.closedSubschemeDeltaDimension δ Z = (n : EInt)) :
    sub_zero n ▸
        (Nonnegative.castGrading δ (add_neg_cancel (r : ℤ))
            (hs ▸ comp δ s p (gysinSection δ s r e D) (flatPullback δ p r))).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd n
          (RelativeChow.closedSubschemeClass δ X Z n) =
      RelativeChow.closedSubschemeClass δ X Z n := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The canonical normal virtual bundle of a section of a smooth morphism, with
regularity and finite local freeness derived from the section equation. -/
def sectionNormalBundle {S : Scheme.{u}} {X P : Over S}
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) :=
  @ofNormalSheafOfRankLoci X.left P.left s.left
    (Scheme.Hom.Section.isImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs))
    (@conormalSheaf_isFiniteLocallyFree X.left P.left s.left
      (Scheme.Hom.Section.isRegularImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs)))

/-- A chosen model of deformation to the normal cone of a smooth section, with its
canonical normal bundle. Canonical production of this model is a library follow-up. -/
abbrev SectionSpecializationOfRankLoci {S : Scheme.{u}} {X P : Over S}
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) :=
  @NormalSpecializationOfRankLoci S X P s
    (Scheme.Hom.Section.isImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs))
    (@conormalSheaf_isFiniteLocallyFree X.left P.left s.left
      (Scheme.Hom.Section.isRegularImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs)))

/-- The normal-rank open of a smooth section, with the immersion certificate derived
from its section equation. -/
def sectionNormalRank {S : Scheme.{u}} {X P : Over S}
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) (r : ℕ) : X.left.Opens :=
  @rankOpen X.left P.left s.left
    (Scheme.Hom.Section.isImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs))
    (sectionNormalBundle p s hs) r

/-- The normal rank of a smooth section equals the smooth relative dimension along
that section, on every clopen rank locus. -/
theorem sectionNormalRank_eq_relativeDimensionLocus
    {S : Scheme.{u}} {X P : Over S}
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X) (r : ℕ) :
    sectionNormalRank p s hs r = s.left ⁻¹ᵁ smoothRelativeDimensionLocus p.left r := sorry

/-- Every integer-degree coefficient of normal Gysin for a smooth section composed with
smooth flat pullback, assembled on the common normal-rank and smooth-dimension loci. -/
def sectionCompositeDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X)
    (D : SectionSpecializationOfRankLoci p s hs) (n : ℤ) :
    BivariantClass δ (𝟙 X) n :=
  @factorizationClassDegree S _ δ _ X X P _ _ _ (𝟙 X) s p
    (Scheme.Hom.Section.isRegularImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs))
    inferInstance hs
    (@bidualityIsoOfRankLoci X.left P.left s.left
      (@conormalSheaf_isFiniteLocallyFree X.left P.left s.left
        (Scheme.Hom.Section.isRegularImmersion (congrArg (fun f : X ⟶ X ↦ f.left) hs))))
    D n

/-- The smooth-section composite is the coefficient of its geometric identity
factorization, using canonical biduality and the chosen deformation model. -/
theorem sectionCompositeDegree_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) [IsRegularImmersion s.left] (hs : s ≫ p = 𝟙 X)
    (D : SectionSpecializationOfRankLoci p s hs) (n : ℤ) :
    sectionCompositeDegree δ p s hs D n =
      factorizationClassDegree δ (𝟙 X) s p hs (bidualityIsoOfRankLoci s.left) D n := sorry

end AlgebraicGeometry.BivariantClass.Gysin

namespace AlgebraicGeometry.BivariantClass

open Gysin

/-- A section of a smooth morphism is a regular immersion, and its normal Gysin class
composed with smooth flat pullback is the identity in every integer degree. The datum `D`
is a chosen model of deformation to the normal cone; canonical production of this model
is a library follow-up. -/
theorem gysin_section_comp_flatPullback_eq_oneOfRankLoci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X)
    (D : SectionSpecializationOfRankLoci p s hs) :
    IsRegularImmersion s.left ∧ ∀ n : ℤ,
      sectionCompositeDegree δ p s hs D n =
        if h : n = 0 then h.symm ▸ oneOver δ X else pointwiseZero δ (𝟙 X) n := sorry

end AlgebraicGeometry.BivariantClass
