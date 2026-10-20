/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FinitePresentation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.19.4: if `f : X ⟶ Y` is proper and of finite presentation, its fibres have
dimension at most `d`, and `ℱ` is a finitely presented `𝒪_X`-module, then
`R^d f_* ℱ` is a finitely presented `𝒪_Y`-module. -/
@[stacks 0EX5] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.isFinitePresentation_topDegree :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
      (d : ℕ) [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f d]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation],
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ d).IsFinitePresentation)
