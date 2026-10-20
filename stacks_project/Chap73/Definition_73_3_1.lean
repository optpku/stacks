/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap73.Definition_73_3_1_Precoverage
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 73.3.1: a Zariski covering of an algebraic space `X` over a scheme
`S` is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}` of algebraic spaces over
`S` such that each `f_i` is an open immersion and `|X| = ⋃_i |f_i|(|X_i|)`, i.e.
the morphisms are jointly surjective. -/
@[stacks 041G] #check
  (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_zariskiPrecoverage_iff :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {T : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} (X : I → AlgebraicGeometry.AlgebraicSpace S)
      (f : ∀ i, X i ⟶ T),
      CategoryTheory.Presieve.ofArrows X f ∈
          AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage S T ↔
        (∀ i, AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion (f i)) ∧
          (⋃ i, Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map (f i))) =
            Set.univ)
