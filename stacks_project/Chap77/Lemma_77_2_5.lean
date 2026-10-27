/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity.Henselization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.Impurity

universe u

/- Lemma 77.2.5: in Situation 77.2.1, impurity existence over the strict
henselization, failure of specialization into the closed fibre for some relative
associated point, existence over an étale neighbourhood, and existence over a
morphism quasi-finite at the special point are equivalent.

Authorized correction of the printed source: condition (2) lost a negation.
It means that some relative associated point does not specialize to any point
of the closed fibre, as required by the definition of an impurity. -/
@[stacks 0CVB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.Impurity.existence_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.liesOver y),
    List.TFAE
      [exists_strictHenselization F f y ybar,
        exists_relativeAssassin_not_specializes_closedFiber F f y ybar,
        exists_etaleNeighbourhood F f y, exists_quasiFiniteAt F f y])
