/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Diagonal
import StacksCheckRecall

/-!
# Lemma 108.10.1

The relative diagonal of the functor of relative morphisms `Mor_B(Y, X)` over
`B` is a closed immersion of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 108.10.1 (1): the diagonal of `Mor_B(Y, X)` over `B` is a closed immersion. -/
@[stacks 0DPM]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isClosedImmersion_diagonal :
  ∀ {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x],
    SchemeOver.IsClosedImmersion
      (Limits.diag (AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor y x)))

/- Lemma 108.10.1 (2): the diagonal of `Mor_B(Y, X)` over `B` is of finite
presentation. -/
@[stacks 0DPM]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.finitePresentation_diagonal :
  ∀ {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x],
    SchemeOver.IsFinitePresentation
      (Limits.diag (AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor y x)))
