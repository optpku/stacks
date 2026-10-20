/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Irreducible
import StacksCheckRecall

/-! @stack 02UW -/

@[expose] public section

/-
Lemma 20.20.2 (02UW): if `X` is irreducible, then the positive-degree cohomology of
the constant additive sheaf with value `A` vanishes.

The reusable owner first records that the constant sheaf is flasque.  Canonical sheafification,
Grothendieck, and `HasExt` instances are inferred by ReasLib, so neither the owner nor this recall
exposes them as mathematical hypotheses.
-/
@[stacks 02UW "higher cohomology of a constant sheaf on an irreducible space"]
#check @TopCat.Sheaf.Constant.isZero_cohomology

#check @TopCat.Sheaf.Constant.isFlasque_of_irreducible

end
