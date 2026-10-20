/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TopologicalInvariance

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback.isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsIntegralHom f] [UniversallyInjective f] [Surjective f],
      (spacesEtalePullback f).IsEquivalence)

end AlgebraicGeometry.AlgebraicSpace
