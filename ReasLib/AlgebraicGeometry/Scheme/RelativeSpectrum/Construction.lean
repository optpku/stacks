/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Basic
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization

/-!
# Chosen models of relative spectra

Relative-spectrum representability is proposition-valued. This leaf therefore
uses explicit chosen models rather than extracting a scheme noncomputably from
a representability proof.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- An explicit candidate model for the relative spectrum of a quasi-coherent algebra sheaf.
The scheme, structure morphism, and universal map are data. Its representability and
affine-local realization are kept in the separate proposition `IsRelativeSpectrumOver`. -/
structure RelativeSpectrumOver (A : S.QcAlgebraUnder) where
  /-- The scheme underlying the chosen relative spectrum. -/
  scheme : Scheme.{u}
  /-- The structural morphism to the base scheme. -/
  π : scheme ⟶ S
  /-- The universal algebra map to the pushforward of the chosen structure sheaf. -/
  universalMap : A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap π.toShHom)

namespace RelativeSpectrumOver

/-- Construct a relative-spectrum candidate from explicit point data. -/
def ofPoint (A : S.QcAlgebraUnder) {X : Scheme.{u}} (π : X ⟶ S)
    (universalMap : A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap π.toShHom)) :
    RelativeSpectrumOver A :=
  { scheme := X
    π
    universalMap }

/-- The universal relative-spectrum point carried by a chosen model. -/
def point (P : RelativeSpectrumOver A) : relativeSpectrumPair A P.scheme :=
  ⟨P.π, P.universalMap⟩

end RelativeSpectrumOver

section

variable {A : S.QcAlgebraUnder}

/-- A relative-spectrum candidate has the expected universal property and affine-local
realization. Keeping this condition proposition-valued prevents the underlying scheme and
universal map from depending on a deferred proof. -/
class IsRelativeSpectrumOver (P : RelativeSpectrumOver A) : Prop where
  /-- The universal point represents the relative-spectrum functor. -/
  isRepresentedBy :
    (relativeSpectrumFunctor A).IsRepresentedBy (P.point : relativeSpectrumPair A P.scheme)
  /-- The structural morphism has the expected affine-local realization. -/
  realizes : realizesRelativeSpectrum A P.π

/-- The scheme underlying an explicit chosen relative-spectrum model. -/
abbrev relativeSpec (P : RelativeSpectrumOver A) : Scheme.{u} :=
  P.scheme

/-- The universal point of an explicit chosen relative-spectrum model. -/
abbrev relativeSpecPoint (P : RelativeSpectrumOver A) : relativeSpectrumPair A (relativeSpec P) :=
  P.point

/-- The structural morphism of an explicit chosen relative-spectrum model. -/
abbrev relativeSpecπ (P : RelativeSpectrumOver A) : P.scheme ⟶ S :=
  P.π

/-- The universal algebra map of an explicit chosen relative-spectrum model. -/
abbrev relativeSpecUniversalFamily (P : RelativeSpectrumOver A) :
    A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap P.π.toShHom) :=
  P.universalMap

/-- The universal point of a relative-spectrum model represents the relative-spectrum functor. -/
theorem relativeSpecPoint_isRepresentedBy (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P] :
    (relativeSpectrumFunctor A).IsRepresentedBy (relativeSpecPoint P) :=
  IsRelativeSpectrumOver.isRepresentedBy

/-- The structural morphism of a relative-spectrum model realizes the relative spectrum. -/
theorem relativeSpecπ_realizesRelativeSpectrum (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P] :
    realizesRelativeSpectrum A (relativeSpecπ P) :=
  IsRelativeSpectrumOver.realizes

end

end AlgebraicGeometry.Scheme
