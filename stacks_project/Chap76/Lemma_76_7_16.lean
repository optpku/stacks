/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 76.7.16: let `S` be a scheme. Let `f : X ⟶ Y` be a smooth morphism of algebraic
spaces over `S`. Then `Ω[f]` is a finite locally free `𝒪_X`-module. -/
@[stacks 0CK5] #check
  (AlgebraicGeometry.AlgebraicSpace.isFiniteLocallyFree_relativeDifferentials_of_smooth :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Smooth f],
      (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f).IsFiniteLocallyFree)
