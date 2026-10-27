/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveFormulaMap
import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.Operational
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern.Commutation
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernComparison
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernInvertibleSequence
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.IteratedFirstChern
import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Degree
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectivePushforward
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

/- Lemma 82.21.2: In Situation 82.2.1, for good `X / B` and invertible `L` on
`X`, the cycle-level operation `Hom.firstChernClassCap f δ L k` factors through
`RationalEquivalence.boundaries` by `FirstChernChow.boundaries_le_ker`, inducing
the additive operation
`FirstChernChow.cap f δ L k : Hom.chowGroup f δ (k + 1) →+ Hom.chowGroup f δ k`.
On cycle representatives, `FirstChernChow.cap_mk` recovers `c1(L) ∩ -`. -/
@[stacks 0EQY]
#check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow.cap :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
      [IsDimensionFunction δ] (L : X.Modules) [isInvertibleObject L]
      (k : ℤ), Hom.chowGroup f δ (k + 1) →+ Hom.chowGroup f δ k)
