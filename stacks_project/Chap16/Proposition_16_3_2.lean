/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.QuotientLift.Smooth

@[expose] public section

/- Proposition 16.3.2 (1): syntomic algebras lift along arbitrary surjective
base maps, with a compatible identification after quotienting by the kernel. -/
@[stacks 07M8 "syntomic algebras lift along surjections"]
#check @Algebra.Syntomic.exists_lift_of_surjective

/- Proposition 16.3.2 (2): smooth algebras lift along arbitrary surjective
base maps, with a compatible identification after quotienting by the kernel. -/
@[stacks 07M8 "smooth algebras lift along surjections"]
#check @Algebra.Smooth.exists_lift_of_surjective

/- Canonical quotient forms used to construct the source-facing bridges. -/
#check @Algebra.Syntomic.exists_lift_of_quotient
#check @Algebra.Smooth.exists_lift_of_quotient
