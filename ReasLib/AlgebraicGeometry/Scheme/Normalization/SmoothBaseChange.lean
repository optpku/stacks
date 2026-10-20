/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a morphism realizing the relative spectrum of a quasi-coherent algebra, normalization
commutes with smooth base change. -/
theorem isIso_normalizationPullback_of_realizesRelativeSpectrum
    {X Y Z : Scheme.{u}} (A : X.QcAlgebraUnder) (π : Z ⟶ X)
    (hπ : Scheme.realizesRelativeSpectrum A π) (f : Y ⟶ X) [Smooth f] :
    -- Local instance justification (proof-local temporary data): affineness is derived only to elaborate the canonical normalization comparison without registering an instance.
    letI : IsAffineHom π := Scheme.isAffineHom_of_realizesRelativeSpectrum A hπ
    IsIso (π.normalizationPullback f) := sorry

/-- Normalization of a quasi-compact, quasi-separated morphism commutes with smooth base
change. -/
theorem isIso_normalizationPullback_of_smooth
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Smooth g] :
    IsIso (f.normalizationPullback g) := sorry

end AlgebraicGeometry.Scheme.Hom
