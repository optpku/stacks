/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Resolution.Surface
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace IsLocalRing

universe u

#check (AlgebraicGeometry.AlgebraicSpace.hasFiniteNormalizationNormalCompletions :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsIntegral Y],
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.hasFiniteNormalizationNormalCompletions_iff :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y],
    hasFiniteNormalizationNormalCompletions Y ↔
      IsFinite Y.normalizationTo ∧
        Set.Finite (setOf fun (y : Points Y.normalization) ↦ ¬ RegularAt Y.normalization y) ∧
          ∀ (y : Points Y.normalization), ¬ RegularAt Y.normalization y →
            IsNormalRing
              (AdicCompletion (maximalIdeal (henselianLocalRing Y.normalization y))
                (henselianLocalRing Y.normalization y)))

/- Theorem 89.8.3: Let `S` be a scheme. Let `Y` be a two dimensional integral Noetherian
algebraic space over `S`. The following are equivalent: there exists an alteration `X ⟶ Y`
with `X` regular, there exists a resolution of singularities of `Y`, `Y` has a resolution of
singularities by normalized blowups, the normalization `Y.normalizationTo` is finite,
`Y.normalization` has finitely many singular points, and for each such point the completion of
the henselian local ring `henselianLocalRing Y.normalization y` is normal. -/
@[stacks 0BHY] #check (AlgebraicGeometry.AlgebraicSpace.regularAlteration_tfae :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]
      (h_dim : dimension Y = 2),
    List.TFAE
      [ ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
          IsAlteration f ∧ IsRegular X
      , ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y), IsResolution f
      , HasResolutionByNormalizedBlowups Y h_dim
      , hasFiniteNormalizationNormalCompletions Y ])

#check (AlgebraicGeometry.AlgebraicSpace.regularAlteration_iff_resolution :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]
      (h_dim : dimension Y = 2),
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y), IsResolution f)

#check (AlgebraicGeometry.AlgebraicSpace.regularAlteration_iff_normalizedBlowups :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]
      (h_dim : dimension Y = 2),
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      HasResolutionByNormalizedBlowups Y h_dim)

#check (AlgebraicGeometry.AlgebraicSpace.regularAlteration_iff_finiteNormalization_normalCompletions :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]
      (h_dim : dimension Y = 2),
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      hasFiniteNormalizationNormalCompletions Y)
