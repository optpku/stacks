/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.Curve
import StacksCheckRecall

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.15.1 (1): a one-dimensional integral Noetherian scheme admits an alteration from
a regular integral scheme if and only if its normalization morphism is finite. -/
@[stacks 0BI4] #check
  (AlgebraicGeometry.Scheme.existsRegularAlteration_iff_isFiniteNormalizationTo :
    ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y],
      topologicalKrullDim Y = 1 →
    ((∃ (X : Scheme.{u}) (hX : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ Regular X) ↔
      IsFinite (AlgebraicGeometry.Scheme.normalizationToOfIsNoetherian Y)))

/- Lemma 54.15.1 (2): a one-dimensional integral Noetherian scheme admits a resolution of
singularities if and only if its normalization morphism is finite. -/
@[stacks 0BI4] #check
  (AlgebraicGeometry.Scheme.existsResolution_iff_isFiniteNormalizationTo :
    ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y],
      topologicalKrullDim Y = 1 →
    ((∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f) ↔
      IsFinite (AlgebraicGeometry.Scheme.normalizationToOfIsNoetherian Y)))

/- Lemma 54.15.1 (3): a one-dimensional integral Noetherian scheme admits a finite sequence
of blowups at closed points with regular terminal scheme if and only if its normalization
morphism is finite. -/
@[stacks 0BI4] #check
  (AlgebraicGeometry.Scheme.existsRegularPointBlowupSequence_iff_isFiniteNormalizationTo :
    ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y],
      topologicalKrullDim Y = 1 →
    ((∃ (X : Scheme.{u}) (_ : PointBlowupSequence Y X), Regular X) ↔
      IsFinite (AlgebraicGeometry.Scheme.normalizationToOfIsNoetherian Y)))

end AlgebraicGeometry.Scheme
