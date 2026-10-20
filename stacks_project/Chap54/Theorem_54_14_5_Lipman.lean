/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.Surface
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Theorem 54.14.5 (Lipman) (1) -/
@[stacks 0BGP]
#check (AlgebraicGeometry.Scheme.regularAlteration_iff_resolution :
  ∀ (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y],
    topologicalKrullDim Y = 2 →
      ((∃ (X : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsIntegral X)
            (f : X ⟶ Y),
          AlgebraicGeometry.IsAlteration f ∧ AlgebraicGeometry.Scheme.Regular X) ↔
        ∃ (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
          AlgebraicGeometry.IsResolution f))

/- Theorem 54.14.5 (Lipman) (2) -/
@[stacks 0BGP]
#check (AlgebraicGeometry.Scheme.regularAlteration_iff_normalizedBlowups :
  ∀ (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y] (h_dimension : topologicalKrullDim Y = 2),
    ((∃ (X : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsIntegral X)
          (f : X ⟶ Y),
        AlgebraicGeometry.IsAlteration f ∧ AlgebraicGeometry.Scheme.Regular X) ↔
      AlgebraicGeometry.Scheme.HasResolutionByNormalizedBlowups Y h_dimension))

/- Theorem 54.14.5 (Lipman) (3) -/
@[stacks 0BGP]
#check (AlgebraicGeometry.Scheme.regularAlteration_iff_finiteNormalization_normalCompletions :
  ∀ (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y],
    topologicalKrullDim Y = 2 →
      ((∃ (X : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsIntegral X)
            (f : X ⟶ Y),
          AlgebraicGeometry.IsAlteration f ∧ AlgebraicGeometry.Scheme.Regular X) ↔
        AlgebraicGeometry.IsFinite (AlgebraicGeometry.Scheme.normalizationToOfIsNoetherian Y) ∧
          (AlgebraicGeometry.Scheme.singularLocus
            (AlgebraicGeometry.Scheme.normalizationOfIsNoetherian Y)).Finite ∧
          ∀ y : AlgebraicGeometry.Scheme.normalizationOfIsNoetherian Y,
            y ∈ AlgebraicGeometry.Scheme.singularLocus
              (AlgebraicGeometry.Scheme.normalizationOfIsNoetherian Y) →
              IsNormalRing (AdicCompletion
                (IsLocalRing.maximalIdeal
                  ((AlgebraicGeometry.Scheme.normalizationOfIsNoetherian Y).presheaf.stalk y))
                ((AlgebraicGeometry.Scheme.normalizationOfIsNoetherian Y).presheaf.stalk y))))
