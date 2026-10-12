/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Truncation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic cohomology sheaves and truncation bounds

This bridge lets the source-facing acyclicity predicate feed the canonical uniform negative
vanishing criterion for derived-limit truncation comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- Acyclic cohomology sheaves on `B` give the degree-zero uniform negative bound used by the
lower-truncation comparison API. -/
@[stacks 0BKZ "acyclic cohomology sheaves to uniform truncation bound"]
theorem toUniformNegative {B : Set X} {K : RingedSite.Hom.ModuleDerived.{z} X}
    (hK : RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn X B K) :
    RingedSite.Hom.ModuleDerived.Limit.Basis.uniformNegative X K 0 B := sorry

end RingedSite.Hom.ModuleDerived.CohomologySheaves.IsAcyclicOn

end
