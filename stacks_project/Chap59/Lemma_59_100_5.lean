/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleCohomology
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 59.100.5: finite morphisms and small-to-big étale essential-image coefficients
satisfy the weak Serre condition and the five fppf–étale comparison properties. -/
@[stacks 0F0H] #check (AlgebraicGeometry.Scheme.FppfEtale.comparisonSituation.{u} :
  CategoryTheory.GrothendieckTopology.TopologyComparison.Situation.{u + 1, u, u + 1, u + 1, u + 1}
    AlgebraicGeometry.Scheme.fppfTopology AlgebraicGeometry.Scheme.etaleTopology
    (@AlgebraicGeometry.IsFinite : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    (fun X : AlgebraicGeometry.Scheme.{u} ↦ AlgebraicGeometry.Scheme.FppfEtale.essImageAb X))

end
