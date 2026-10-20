/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.12

The reusable derived-limit cohomology comparison is owned by ReasLib and is recalled here with
the canonical basiswise hypotheses.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.12 (0A09): basiswise acyclicity and vanishing of the section `R¹ lim` identify the
degree-`q` cohomology sheaf of a sequential derived limit with the ordinary inverse limit. -/
@[stacks 0A09]
#check @cohomologySheaf_iso_limit_of_basiswise_acyclic
