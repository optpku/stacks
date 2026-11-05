/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Properties
import StacksCheckRecall

/-!
# Lemma 27.4.6 compatibility entry point

Affineness, base change, and universal-map comparison APIs for relative spectra
are owned by ReasLib.
-/

@[expose] public section

universe u

open scoped AlgebraicGeometry

/- The explicit algebra map carried by a relative-spectrum point. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpectrumUniversalMap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}}
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A X),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
        CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap x.1.toShHom))

/- The explicit algebra map carried by a relative-spectrum point over a prescribed morphism. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpectrumUniversalMapOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ S)
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A X) (hxπ : x.1 = π),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
        CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap π.toShHom))

/- The realization-level affine-preimage property used by Lemma 27.4.6 (1). -/
#check
  (AlgebraicGeometry.Scheme.isAffineOpen_preimage_of_realizesRelativeSpectrum :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ S)
      (hπ : AlgebraicGeometry.Scheme.realizesRelativeSpectrum A π)
      (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U),
      AlgebraicGeometry.IsAffineOpen (π ⁻¹ᵁ U))

/- The realization-level base-change property used by Lemma 27.4.6 (2). -/
#check
  (AlgebraicGeometry.Scheme.realizesRelativeSpectrum_pullback_snd :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ S)
      (hπ : AlgebraicGeometry.Scheme.realizesRelativeSpectrum A π)
      (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
      (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A'),
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A'
        (CategoryTheory.Limits.pullback.snd π g))

/- The representability-level universal-map property used by Lemma 27.4.6 (3). -/
#check
  (AlgebraicGeometry.Scheme.isIso_relativeSpectrumUniversalMap_of_isRepresentedBy :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ S)
      (x : AlgebraicGeometry.Scheme.relativeSpectrumPair A X) (hxπ : x.1 = π)
      (hx : (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy x),
      CategoryTheory.IsIso
        (AlgebraicGeometry.Scheme.relativeSpectrumUniversalMapOver A π x hxπ))

/- Lemma 27.4.6 (1): inverse images of affine opens under the relative-spectrum morphism are
affine. -/
@[stacks 01LX] #check
  (AlgebraicGeometry.Scheme.isAffineOpen_preimage_relativeSpec :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P]
      (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U),
      AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.relativeSpecπ P) ⁻¹ᵁ U))

/- Lemma 27.4.6 (2): base change of a relative-spectrum model is a relative-spectrum model for
the explicitly specified pulled-back algebra. -/
@[stacks 01LX] #check
  (AlgebraicGeometry.Scheme.relativeSpecPullbackIso :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P]
      (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
      (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A')
      (P' : AlgebraicGeometry.Scheme.RelativeSpectrumOver A')
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P'],
      CategoryTheory.Over.mk
          (CategoryTheory.Limits.pullback.snd
            (AlgebraicGeometry.Scheme.relativeSpecπ P) g) ≅
        CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.relativeSpecπ P'))

/- The compatibility entry point retains the explicitly constructed inverse. -/
#check
  (AlgebraicGeometry.Scheme.nonempty_iso_over_pullback_relativeSpec_inv :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P]
      (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
      (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A')
      (P' : AlgebraicGeometry.Scheme.RelativeSpectrumOver A')
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P'],
      (AlgebraicGeometry.Scheme.nonempty_iso_over_pullback_relativeSpec
          A P g A' pullbackData P').inv.left =
        AlgebraicGeometry.Scheme.relativeSpecPullbackComparisonInv A P g A' pullbackData P')

/- The comparison is classified by the explicit pulled-back universal point. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecPullbackComparison_point :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
      (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A')
      (P' : AlgebraicGeometry.Scheme.RelativeSpectrumOver A')
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P'],
      AlgebraicGeometry.Scheme.relativeSpectrumPairPullbackMap A'
          (AlgebraicGeometry.Scheme.relativeSpecPullbackComparison A P g A' pullbackData P')
          P'.point =
        AlgebraicGeometry.Scheme.relativeSpecPullbackPoint A P g A' pullbackData)

/- Lemma 27.4.6 (3): the universal algebra map of a relative-spectrum model is an isomorphism. -/
@[stacks 01LX] #check
  (AlgebraicGeometry.Scheme.isIso_relativeSpecUniversalFamily :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeSpecUniversalFamily P))
