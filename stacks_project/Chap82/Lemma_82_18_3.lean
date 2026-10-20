/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import stacks_project.Chap82.«82_18_3_1»

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 82.18.3: In Situation 82.2.1 let `Y / B` be good. Let `ℒ` be an invertible
`𝒪_Y`-module. Let `s` be a regular section of `ℒ` and assume `dim_δ(Y) ≤ k + 1`.
Write `[Y]_{k+1} = ∑ n_i [Y_i]` where `Y_i ⊂ Y` are the irreducible components of
`Y` of `δ`-dimension `k + 1`. Set `s_i = s|_{Y_i}`. Then
`[Z(s)]_k = ∑ n_i [Z(s_i)]_k` as `k`-cycles on `Y`. -/
@[stacks 0EQL]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeZeroCycle_eq_sum_components :
  ∀ {S : Scheme.{u}} {B Y : AlgebraicSpace S} [UniversallyCatenary B]
    (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections)
    [IsRegularSection ℒ s] (k : ℤ),
    (∀ y : Points Y, Hom.relativeDimensionFunction p δ y ≤ k + 1) →
    relativeZeroCycle p δ ℒ s k = relativeZeroCycleComponentSum p δ ℒ s k)
