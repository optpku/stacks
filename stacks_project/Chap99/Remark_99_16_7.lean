/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Stack

/-!
# Remark 99.16.7

In Situation 99.16.3 the rule `(T, g, E) ↦ (T, g)` is a 1-morphism of stacks in
groupoids `Complexes_{X/B} ⟶ 𝒮_B`. For `g : B' ⟶ B`, the square comparing
`Complexes_{X'/B'}` with `Complexes_{X/B}` over `Sch/B' → Sch/B` (equivalently
`𝒮_{B'} → 𝒮_B`) is a 2-fibre product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoricalPullback
open scoped CategoryTheory.Bicategory

universe u

/- Remark 99.16.7 (1): in Situation 99.16.3 the rule `(T, g, E) ↦ (T, g)` defines a
1-morphism `Complexes_{X/B} ⟶ 𝒮_B` of stacks in groupoids. -/
@[stacks 0DLI] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    AlgebraicGeometry.AlgebraicSpace.Complexes.toGroupoids f ⟶
      AlgebraicGeometry.GroupScheme.Classifying.toGroupoids B)

/- Remark 99.16.7 (2): for any `g : B' ⟶ B`, the square of complexes on
`X' = X ×_B B'` and `X` over `Sch/B' → Sch/B` (equivalently `𝒮_{B'} → 𝒮_B`)
is a 2-fibre product square. -/
@[stacks 0DLI] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.square.instIsBilimit :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    CatCommSqOver.Resized.IsBilimit (AlgebraicGeometry.AlgebraicSpace.Complexes.square f g))
