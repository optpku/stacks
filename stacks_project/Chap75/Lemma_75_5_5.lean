/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Preservation
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace CategoryTheory ObjectProperty

universe u

/- Lemma 75.5.5: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. The functor `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
@[stacks 08F4] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback_preservesQuasiCoherent :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y X : AlgebraicGeometry.AlgebraicSpace S}
      (f : Y ⟶ X),
      derivedQuasiCoherentModuleProperty X ≤
        (derivedQuasiCoherentModuleProperty Y).inverseImage (ModuleDerived.pullback f))
