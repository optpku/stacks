/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.OpenImmersion
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-! # The Quot functor map along an open immersion -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Fibrewise pushforward along an open immersion induces the canonical map of Quot functors. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.openMap :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (j : X ⟶ Y) (y : Y ⟶ B)
    (G : Y.Modules) [IsOpenImmersion j]
    [Separated (j ≫ y)] [FinitePresentation (j ≫ y)]
    [Separated y] [FinitePresentation y] [G.IsQuasicoherent],
    AlgebraicGeometry.AlgebraicSpace.Quot.quot (j ≫ y) ((Modules.pullback j).obj G) ⟶
      AlgebraicGeometry.AlgebraicSpace.Quot.quot y G)
