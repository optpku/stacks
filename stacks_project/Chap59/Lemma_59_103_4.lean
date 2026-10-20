/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EtaleCohomology
import StacksCheckRecall

@[expose] public section

universe u i

/- Lemma 59.103.4: the identity comparison ε : (Sch/S)_h ⟶ (Sch/S)_étale,
with P the class of proper morphisms and A'_X the sheaves on (Sch/X)_étale
isomorphic to π_X⁻¹ of a torsion abelian sheaf on X_étale, satisfies
properties (1)–(5) of Situation 21.30.1. -/
@[stacks 0F0J]
#check (AlgebraicGeometry.Scheme.HComparison.comparisonSituation.{u, i} :
  CategoryTheory.GrothendieckTopology.TopologyComparison.Situation.{u + 1, u, i,
    max (u + 1) i, max (u + 1) i}
    AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck
    AlgebraicGeometry.Scheme.etaleTopology (@AlgebraicGeometry.IsProper)
    (fun X => AlgebraicGeometry.Scheme.HComparison.torsionPullback X))

end
