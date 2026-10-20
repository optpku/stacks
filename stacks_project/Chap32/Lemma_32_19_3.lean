/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FiniteType
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.19.3: if `f : X ⟶ Y` is proper with fibres of dimension at most `d`, and
`ℱ` is a finite-type quasicoherent `𝒪_X`-module, then `R^d f_* ℱ` is a finite-type
quasicoherent `𝒪_Y`-module. Finite type is supplied by the checked theorem below, while
quasicoherence is supplied by the canonical higher-direct-image instance. -/
@[stacks 0EX4] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.isFiniteType_of_proper_of_relativeDimensionLE :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsProper f]
      (d : ℕ) [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f d]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ d).IsFiniteType)
