/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

/- 86.7.0.1: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated algebraic spaces over
a scheme `S`, a right adjoint `a` to `Rf_*`, and `K : DerivedQCoh Y`, the projection formula and
the counit define the canonical map `Lf^*K ⊗ a(𝒪_Y) ⟶ a(K)`. -/
@[stacks 0E5P] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorDualityMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K : DerivedQCoh Y),
      tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K)
