/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Graded.Algebra
import StacksCheckRecall

/-!
# Remark 24.3.2

Pullback, pushforward, and their Hom equivalence act degreewise on the underlying graded module
of a graded algebra sheaf.  The reusable owner works for an arbitrary additive grading monoid.
-/

@[expose] public section

/- Remark 24.3.2 (1) (0FQX): pushforward and pullback of underlying graded algebra objects are
computed degreewise. -/
@[stacks 0FQX]
#check @RingedSite.Hom.Graded.Algebra.pushforward_obj_apply

#check @RingedSite.Hom.Graded.Algebra.pullback_obj_apply

/- Remark 24.3.2 (2) (0FQX): the induced maps are computed degreewise. -/
@[stacks 0FQX]
#check @RingedSite.Hom.Graded.Algebra.pushforward_map_apply

#check @RingedSite.Hom.Graded.Algebra.pullback_map_apply

/- Remark 24.3.2 (3) (0FQX): the graded Hom equivalence is the module-sheaf adjunction in each
degree. -/
@[stacks 0FQX]
#check @RingedSite.Hom.Graded.Algebra.homEquiv_apply_apply
