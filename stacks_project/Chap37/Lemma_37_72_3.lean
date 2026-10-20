/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.DimensionOne

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.72.3 (1): quasicoherent higher direct images vanish above degree one. -/
@[stacks 0E7H] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.vanishesAbove_one_of_fiberH1 :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hH1 : ∀ y : Y,
        IsZero (Scheme.Modules.cohomology
          (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)),
      AlgebraicGeometry.Scheme.HigherDirectImage.VanishesAbove f 1)

/- Lemma 37.72.3 (2): the degree-one higher direct image of a quasicoherent quotient of a
pulled-back quasicoherent module vanishes. -/
@[stacks 0E7H] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.degreeOne_isZero_of_epi_pullback :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hH1 : ∀ y : Y,
        IsZero (Scheme.Modules.cohomology
          (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]
      (π : (Scheme.Modules.pullback f).obj 𝒢 ⟶ ℱ) [Epi π],
      IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ 1))

/- Lemma 37.72.3 (3): over an affine target, quasicoherent cohomology vanishes above degree
one. -/
@[stacks 0E7H] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.globalCohomology_isZero_above_one_of_affine :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hH1 : ∀ y : Y,
        IsZero (Scheme.Modules.cohomology
          (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
      [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (p : ℕ) (hp : 1 < p),
      IsZero (Scheme.Modules.cohomology ℱ p))

/- Lemma 37.72.3 (4): over an affine target, a globally generated quasicoherent module has
vanishing first cohomology. -/
@[stacks 0E7H] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.globalCohomology_degreeOne_isZero_of_globallyGenerated :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hH1 : ∀ y : Y,
        IsZero (Scheme.Modules.cohomology
          (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))
      [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [SheafOfModules.IsGloballyGenerated ℱ],
      IsZero (Scheme.Modules.cohomology ℱ 1))
