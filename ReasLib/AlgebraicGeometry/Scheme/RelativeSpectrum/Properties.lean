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
    IsAffineOpen (relativeSpecπ P ⁻¹ᵁ U) := sorry

/-- Base change identifies an explicit relative-spectrum model with a model of the explicitly
specified pulled-back algebra, as objects over the new base. -/
noncomputable def nonempty_iso_over_pullback_relativeSpec
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (P' : RelativeSpectrumOver A') [IsRelativeSpectrumOver P'] :
    Over.mk (pullback.snd (relativeSpecπ P) g) ≅ Over.mk (relativeSpecπ P') :=
  nonempty_iso_over_of_realizesRelativeSpectrum_and_isRepresentedBy A'
    (realizesRelativeSpectrum_pullback_snd A (relativeSpecπ P)
      (IsRelativeSpectrumOver.realizes (P := P)) g A' pullbackData)
    (relativeSpecPoint P')
    (relativeSpecPoint_isRepresentedBy P')

/-- The universal algebra map carried by an explicit relative-spectrum model is an
isomorphism. -/
theorem isIso_relativeSpecUniversalFamily
    (A : S.QcAlgebraUnder) (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P] :
    IsIso (relativeSpecUniversalFamily P) := sorry

end AlgebraicGeometry.Scheme
