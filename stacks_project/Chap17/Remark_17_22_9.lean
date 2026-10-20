/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Counterexamples.TwoClosedPoints
import StacksCheckRecall

/-!
# Remark 17.22.9

The reusable counterexample is owned by `TopCat.Counterexample.TwoClosedPoints`. Its `Tail`
namespace supplies a filtered system of tail sheaves on a compact space for which global sections
do not preserve the colimit. This file records the integer-valued specialization referenced by the
Stacks Project.
-/

@[expose] public section

open CategoryTheory

/- The underlying two-closed-points space is compact. -/
#check TopCat.Counterexample.TwoClosedPoints.compactSpace

/- The counterexample uses the canonical filtered diagram of integer-valued tail sheaves. -/
#check
  TopCat.Counterexample.TwoClosedPoints.Tail.sheafFunctor (AddCommGrpCat.of ℤ)

/- Its canonical comparison is the map from the colimit of global sections to the global sections
of the colimit sheaf. -/
#check
  TopCat.Counterexample.TwoClosedPoints.Tail.globalSectionsComparison (AddCommGrpCat.of ℤ)

/- Remark 17.22.9 (01BT): compactness alone does not make the global-sections comparison for a
filtered colimit an isomorphism. -/
@[stacks 01BT]
#check
  TopCat.Counterexample.TwoClosedPoints.Tail.globalSectionsComparison_not_isIso_of_nontrivial
    (AddCommGrpCat.of ℤ)
