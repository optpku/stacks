/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn.ExactPushforward
public import ReasLib.AlgebraicGeometry.RingedSite.TopologyComparison
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.29.1 (07A8) uses the canonical topology-comparison morphism
`RingedSite.TopologyComparison.hom`.  Its reusable categorical core is split between the
weak-Serre transfer `RingedSite.Hom.moduleDerivedCohomologyIn.target_isWeakSerre` and the derived
equivalence `pullback_isEquivalence_of_exactPushforward`.  The latter consumes the canonical
`DerivedAdjunction.HasPair` certificate and the explicit pullback basis; it does not ask callers
to choose an arbitrary derived adjunction.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace RingedSite.Hom.moduleDerivedCohomologyIn

@[stacks 07A8 "(1), target weak-Serre transfer"]
#check @target_isWeakSerre

@[stacks 07A8 "(2), derived equivalence"]
#check @pullback_isEquivalence_of_exactPushforward

end RingedSite.Hom.moduleDerivedCohomologyIn

@[stacks 07A8 "topology-comparison morphism"]
#check @RingedSite.TopologyComparison.hom

end
