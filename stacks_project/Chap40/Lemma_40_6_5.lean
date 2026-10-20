/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.TargetLocus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 40.6.5: for a non-Zariski standard topology, the maximal target-open locus
where the stabilizer morphism has a target-local property is invariant under the groupoid. -/
@[stacks 06QQ] #check
  (AlgebraicGeometry.GroupoidScheme.isOpenInvariant_targetLocus_stabilizerMap :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      (τ : StandardTopology) (hτ : τ ≠ .zariski)
      (P : MorphismProperty Scheme.{u}) [P.IsLocalAtTarget τ.precoverage]
      (hs : Presieve.singleton G.s.left ∈ τ.precoverage G.U.left)
      (ht : Presieve.singleton G.t.left ∈ τ.precoverage G.U.left),
      G.toPreRelation.IsOpenInvariant (P.targetLocus G.stabilizerMap.left))

end AlgebraicGeometry
