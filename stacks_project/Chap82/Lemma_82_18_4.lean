/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle.Geometric
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.18.4: In Situation 82.2.1 let `X / B` be good. Let `L` be an
invertible `𝒪_X`-module. Let `Y ⊂ X` be a closed subspace with
`dim_δ(Y) ≤ k + 1` and let `s` be a regular section of `L|_Y`. Then
`c1(L) ∩ [Y]_{k+1} = [Z(s)]_k` in `CH_k(X)`. -/
@[stacks 0EQN]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_closedSubspace_eq_zeroSchemeCycle :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : X.Modules) [isInvertibleObject L] (Y : ClosedSubspace X)
    (s : ((Modules.pullback Y.ι).obj L).sections)
    [IsRegularSection ((Modules.pullback Y.ι).obj L) s] (k : ℤ),
    closedSubspaceDeltaDimension f δ Y ≤ ((k + 1 : ℤ) : EInt) →
    firstChernClassCap f δ L k (closedSubspaceCycleInDegree f δ Y (k + 1)) =
      chowMk f δ k
        (closedSubspaceCycleInDegree f δ (ClosedSubspace.zeroSchemeRestrict Y L s) k))

