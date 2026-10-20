/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.SmoothBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.19.1: Smooth base change preserves the integral closure of a
quasi-coherent algebra, expressed through the canonical normalization comparison. -/
@[stacks 081K] #check
  (AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_of_realizesRelativeSpectrum :
    ∀ {X Y Z : Scheme.{u}} (A : X.QcAlgebraUnder) (π : Z ⟶ X)
      (hπ : Scheme.realizesRelativeSpectrum A π) (f : Y ⟶ X) [Smooth f],
      -- Local instance justification (proof-local temporary data): derived affineness is used only to elaborate the canonical normalization comparison.
      letI : IsAffineHom π := Scheme.isAffineHom_of_realizesRelativeSpectrum A hπ
      IsIso (π.normalizationPullback f))
