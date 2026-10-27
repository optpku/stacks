/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
import StacksCheckRecall

/-!
# Definition 82.18.1

Intersection with the first Chern class of an invertible module on a good
algebraic space, as an additive operation from `(k + 1)`-cycles to `CH_k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Definition 82.18.1: In Situation 82.2.1, for good `X / B` and an invertible
`𝒪_X`-module `L`, intersection with the first Chern class is the operation
`c1(L) ∩ - = Hom.firstChernClassCap f δ L k : Z_{k+1}(X) →+ CH_k(X)`. On an
integral closed subspace `i : W → X` of `δ`-dimension `k + 1` it is
`i_*(c1(i^* L) ∩ [W])` as in `Hom.firstChernClassCap_closedSubspace`, using
Definition 82.17.1 on `W`, and it extends linearly to a general
`(k + 1)`-cycle `α = ∑ n_i [W_i]` by `Hom.firstChernCycle`. -/
@[stacks 0EQJ]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (L : X.Modules) [isInvertibleObject L] (k : ℤ),
    Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup f δ k)
