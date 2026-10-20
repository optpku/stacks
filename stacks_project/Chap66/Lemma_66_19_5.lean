/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicSpace GeometricPoint

universe u v

@[expose] public section

/- Lemma 66.19.5: for a scheme `S`, an algebraic space `X` over `S`, a geometric point `xbar`
of `X`, an étale neighborhood `U` of `xbar`, and an étale covering in `X_spaces,étale` of the
underlying object of `U`, some member of the covering admits a lift of `xbar` making the covering
map a morphism of étale neighborhoods. -/
@[stacks 04JX] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.exists_lift_of_cover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (U : EtaleNeighborhood xbar)
    {I : Type v} (V : I → spacesEtaleSite X)
    (φ : ∀ i, V i ⟶ U.toSpacesEtale),
    Sieve.ofArrows V φ ∈ spacesEtaleTopology X U.toSpacesEtale →
    ∃ (i : I) (u_i : ofOver xbar.overObj ⟶ (V i).left),
      u_i ≫ (V i).hom = xbar.hom ∧ u_i ≫ (φ i).left = U.lift)
