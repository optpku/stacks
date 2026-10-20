/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Forget
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.BaseChange
public import stacks_project.Chap99.Lemma_99_5_4

/-!
# Remark 99.5.5

For a finite-presentation morphism `f : X ⟶ B` of algebraic spaces over a scheme `S`,
forgetting the module gives `Coh_{X/B} ⟶ 𝒮_B`. For any `g : B' ⟶ B`, the associated
square over `Sch/B' → Sch/B` is a 2-fibre product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoricalPullback

noncomputable section

universe u

/- Remark 99.5.5 (1): the rule `(T, g, F) ↦ (T, g)` defines a 1-morphism
`Coh_{X/B} ⟶ 𝒮_B` of stacks in groupoids in Situation 99.5.1. -/
@[stacks 08LP] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f],
    AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids f ⟶
      AlgebraicGeometry.GroupScheme.Classifying.toGroupoids B)

/- Remark 99.5.5 (2): for every `g : B' ⟶ B`, the canonical square comparing
`Coh_{X ×_B B'/B'}` and `Coh_{X/B}` over `Sch/B' → Sch/B` is a 2-fibre product square. -/
@[stacks 08LP] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.square.instIsBilimit :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
    [FinitePresentation f],
    CatCommSqOver.Resized.IsBilimit (AlgebraicGeometry.AlgebraicSpace.CohStack.square f g))
