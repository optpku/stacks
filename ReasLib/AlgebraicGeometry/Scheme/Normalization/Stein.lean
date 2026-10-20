/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward.Integral
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S S' : Scheme.{u}}

/-- The structural morphism from the relative normalization of a universally closed,
quasi-separated morphism realizes the relative spectrum of its pushed-forward structure sheaf. -/
theorem fromNormalization_realizesRelativeSpectrum
    (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f] :
    Scheme.realizesRelativeSpectrum
      (Scheme.pushforwardStructureSheafQcAlgebra f) f.fromNormalization := sorry

/-- For the relative normalization of a universally closed, quasi-separated morphism,
the canonical map `𝒪_{f.normalization} ⟶ f.toNormalization_* 𝒪_X` is an isomorphism. -/
instance instIsIsoPushforwardMapToNormalization
    (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f] :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toNormalization.toShHom) := sorry

/-- Relative normalization commutes with flat base change through the canonical normalization
comparison morphism. -/
instance instIsIsoNormalizationPullbackOfFlat
    (f : X ⟶ S) (g : S' ⟶ S) [QuasiSeparated f] [UniversallyClosed f] [Flat g] :
    IsIso (f.normalizationPullback g) := sorry

end AlgebraicGeometry.Scheme.Hom
