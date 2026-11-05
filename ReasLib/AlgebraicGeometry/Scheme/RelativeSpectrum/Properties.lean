/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Representability

/-!
# Properties of relative-spectrum models

This leaf contains affineness, base-change, and comparison APIs for relative
spectra. Chosen comparison isomorphisms are explicit data, so no scheme-valued
choice is extracted from a proposition-only existence theorem.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}

/-- The inverse image of an affine open under a relative-spectrum realization is affine. -/
theorem isAffineOpen_preimage_of_realizesRelativeSpectrum
    (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S)
    (hπ : realizesRelativeSpectrum A π) (U : S.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (π ⁻¹ᵁ U) := sorry

/-- Base change of a realization of a relative spectrum is a realization of the explicitly
specified pullback algebra. -/
theorem realizesRelativeSpectrum_pullback_snd
    (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S)
    (hπ : realizesRelativeSpectrum A π) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    realizesRelativeSpectrum A' (pullback.snd π g) := sorry

/-- A representing point induces an isomorphism on its universal algebra map. -/
theorem isIso_relativeSpectrumUniversalMap_of_isRepresentedBy
    (A : S.QcAlgebraUnder) {X : Scheme.{u}}
    (π : X ⟶ S) (x : relativeSpectrumPair A X)
    (hxπ : x.1 = π)
    (hx : (relativeSpectrumFunctor A).IsRepresentedBy x) :
    IsIso (relativeSpectrumUniversalMapOver A π x hxπ) := sorry

/-- The inverse image of an affine open under the structural morphism of an explicit
relative-spectrum model is affine. -/
theorem isAffineOpen_preimage_relativeSpec
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (U : S.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (relativeSpecπ P ⁻¹ᵁ U) :=
  isAffineOpen_preimage_of_realizesRelativeSpectrum A P.π
    (IsRelativeSpectrumOver.realizes (P := P)) U hU

/-- The morphism to a specified model classified by a relative-spectrum point.
The inverse hom correspondence uses the supplied universal-property hypothesis. -/
def relativeSpecLift
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    {T : Scheme.{u}} (p : relativeSpectrumPair A T) : T ⟶ P.scheme :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := P)).representableBy.homEquiv.symm p

/-- The point classified by `relativeSpecLift` is the given point. -/
@[simp]
theorem relativeSpecLift_point
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    {T : Scheme.{u}} (p : relativeSpectrumPair A T) :
    relativeSpectrumPairPullbackMap A (relativeSpecLift A P p) P.point = p :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := P)).representableBy.homEquiv.apply_symm_apply p

/-- The classified morphism preserves the point's structure map. -/
@[simp]
theorem relativeSpecLift_toBase
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    {T : Scheme.{u}} (p : relativeSpectrumPair A T) :
    relativeSpecLift A P p ≫ P.π = p.1 :=
  congrArg Sigma.fst (relativeSpecLift_point A P p)

/-- The universal point on the scheme pullback, transported through the algebra pullback
correspondence. This construction uses the given point of `P`, not a chosen realization. -/
def relativeSpecPullbackPoint
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A)
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumPair A' (pullback P.π g) :=
  ⟨pullback.snd P.π g, (pullbackData.homEquiv (pullback.snd P.π g)).symm
    ((pullback.condition (f := P.π) (g := g)) ▸
      (P.universalMap ≫ relativeSpectrumPairTargetMap P.π (pullback.fst P.π g)))⟩

/-- The canonical base-change comparison, classified by the pulled-back universal point. -/
def relativeSpecPullbackComparison
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A)
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    pullback P.π g ⟶ P'.scheme :=
  relativeSpecLift A' P' (relativeSpecPullbackPoint A P g A' pullbackData)

/-- The comparison is over the new base. -/
theorem relativeSpecPullbackComparison_toBase
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A)
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    relativeSpecPullbackComparison A P g A' pullbackData P' ≫ P'.π =
      pullback.snd P.π g :=
  relativeSpecLift_toBase A' P' _

/-- The inverse comparison comes from the universal point on `P'` and the scheme pullback. -/
def relativeSpecPullbackComparisonInv
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') (P' : RelativeSpectrumOver A') :
    P'.scheme ⟶ pullback P.π g :=
  pullback.lift
    (relativeSpecLift A P ⟨P'.π ≫ g, pullbackData.homEquiv P'.π P'.universalMap⟩)
    P'.π (relativeSpecLift_toBase A P _)

/-- The two explicitly classified comparison maps compose to the identity on the pullback. -/
theorem relativeSpecPullbackComparison_hom_inv_id
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    relativeSpecPullbackComparison A P g A' pullbackData P' ≫
      relativeSpecPullbackComparisonInv A P g A' pullbackData P' = 𝟙 _ := sorry

/-- The two explicitly classified comparison maps compose to the identity on `P'`. -/
theorem relativeSpecPullbackComparison_inv_hom_id
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    relativeSpecPullbackComparisonInv A P g A' pullbackData P' ≫
      relativeSpecPullbackComparison A P g A' pullbackData P' = 𝟙 _ := sorry

/-- The canonical comparison is invertible, with the explicitly constructed inverse. -/
theorem relativeSpecPullbackComparison_isIso
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    IsIso (relativeSpecPullbackComparison A P g A' pullbackData P') :=
  ⟨⟨relativeSpecPullbackComparisonInv A P g A' pullbackData P',
    relativeSpecPullbackComparison_hom_inv_id A P g A' pullbackData P',
    relativeSpecPullbackComparison_inv_hom_id A P g A' pullbackData P'⟩⟩

/-- Base change identifies the two models via explicit forward and inverse morphisms. -/
def relativeSpecPullbackIso
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    Over.mk (pullback.snd (relativeSpecπ P) g) ≅ Over.mk (relativeSpecπ P') :=
  Over.isoMk
    { hom := relativeSpecPullbackComparison A P g A' pullbackData P'
      inv := relativeSpecPullbackComparisonInv A P g A' pullbackData P'
      hom_inv_id := relativeSpecPullbackComparison_hom_inv_id A P g A' pullbackData P'
      inv_hom_id := relativeSpecPullbackComparison_inv_hom_id A P g A' pullbackData P' }
    (relativeSpecPullbackComparison_toBase A P g A' pullbackData P')

/-- The forward component of the base-change isomorphism is the point-classified comparison. -/
@[simp]
theorem relativeSpecPullbackIso_hom
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    (relativeSpecPullbackIso A P g A' pullbackData P').hom.left =
      relativeSpecPullbackComparison A P g A' pullbackData P' := rfl

/-- The inverse component is the explicit morphism into the scheme pullback. -/
@[simp]
theorem relativeSpecPullbackIso_inv
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    (relativeSpecPullbackIso A P g A' pullbackData P').inv.left =
      relativeSpecPullbackComparisonInv A P g A' pullbackData P' := rfl

/-- Compatibility name for the canonical base-change isomorphism. -/
abbrev nonempty_iso_over_pullback_relativeSpec
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    Over.mk (pullback.snd (relativeSpecπ P) g) ≅ Over.mk (relativeSpecπ P') :=
  relativeSpecPullbackIso A P g A' pullbackData P'

/-- The base-change isomorphism has the canonical point-classified forward morphism. -/
@[simp]
theorem nonempty_iso_over_pullback_relativeSpec_hom
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    (nonempty_iso_over_pullback_relativeSpec A P g A' pullbackData P').hom.left =
      relativeSpecPullbackComparison A P g A' pullbackData P' := rfl

/-- The compatibility isomorphism retains the explicitly classified inverse into the
scheme pullback, without using a comparison obtained from a bare realization proof. -/
@[simp]
theorem nonempty_iso_over_pullback_relativeSpec_inv
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    (nonempty_iso_over_pullback_relativeSpec A P g A' pullbackData P').inv.left =
      relativeSpecPullbackComparisonInv A P g A' pullbackData P' := rfl

/-- The comparison pulls the target universal point back to the explicit pullback point. -/
theorem relativeSpecPullbackComparison_point
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A)
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    relativeSpectrumPairPullbackMap A'
        (relativeSpecPullbackComparison A P g A' pullbackData P') P'.point =
      relativeSpecPullbackPoint A P g A' pullbackData :=
  relativeSpecLift_point A' P' _

/-- The universal algebra map carried by an explicit relative-spectrum model is an
isomorphism. -/
theorem isIso_relativeSpecUniversalFamily
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P] :
    IsIso (relativeSpecUniversalFamily P) := sorry

end AlgebraicGeometry.Scheme
