/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Pullback
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
import StacksCheckRecall

/-! # Flat pullback of the quasi-coherent coreflector -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 103.10.3: The quasi-coherent coreflector commutes with pullback along
a flat morphism of algebraic stacks. -/
@[stacks 0GQJ] #check
  (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toQCoh_pullbackIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [AlgebraicStack.Flat f],
      LQCohFbc.inverseImage f ⋙ LQCohFbc.toQCoh X ≅
        LQCohFbc.toQCoh Y ⋙ QCoh.pullback f)
