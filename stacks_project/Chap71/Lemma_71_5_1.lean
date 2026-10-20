/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.5.1: Formation of Fitting ideals of finite-type quasi-coherent
modules on algebraic spaces commutes with inverse image along every morphism. -/
@[stacks 0CZ4] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf_pullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ),
      (fittingIdealSheaf F i).pullback f =
        fittingIdealSheaf ((Modules.pullback f).obj F) i)
