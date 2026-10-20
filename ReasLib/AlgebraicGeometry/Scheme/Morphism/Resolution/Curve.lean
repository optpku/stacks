/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration.RegularSource
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A one-dimensional integral Noetherian scheme admits an alteration from a regular integral
scheme if and only if its normalization morphism is finite. -/
theorem existsRegularAlteration_iff_isFiniteNormalizationTo
    (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : topologicalKrullDim Y = 1) :
    (∃ (X : Scheme.{u}) (hX : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ Regular X) ↔
      IsFinite (normalizationToOfIsNoetherian Y) := sorry

/-- A one-dimensional integral Noetherian scheme admits a resolution of singularities if and
only if its normalization morphism is finite. -/
theorem existsResolution_iff_isFiniteNormalizationTo
    (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : topologicalKrullDim Y = 1) :
    (∃ (X : Scheme.{u}) (f : X ⟶ Y), IsResolution f) ↔
      IsFinite (normalizationToOfIsNoetherian Y) := sorry

/-- A one-dimensional integral Noetherian scheme admits a finite sequence of blowups at closed
points with regular terminal scheme if and only if its normalization morphism is finite. -/
theorem existsRegularPointBlowupSequence_iff_isFiniteNormalizationTo
    (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : topologicalKrullDim Y = 1) :
    (∃ (X : Scheme.{u}) (_ : PointBlowupSequence Y X), Regular X) ↔
      IsFinite (normalizationToOfIsNoetherian Y) := sorry

end AlgebraicGeometry.Scheme
