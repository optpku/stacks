/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.StandardSmooth
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.137.5

@stack 00T6
-/

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

/- Definition 10.137.5: a standard smooth `R`-algebra is the canonical notion
`Algebra.IsStandardSmooth`; it is presented by a quotient of a polynomial algebra by finitely many
relations together with an invertible Jacobian determinant in the quotient. -/
@[stacks 00T6 "standard smooth algebra predicate"]
#check @IsStandardSmooth

/- A submersive presentation packages the quotient presentation and Jacobian-unit condition used in
the definition of a standard smooth algebra. -/
@[stacks 00T6 "standard smooth presentation data"]
#check @SubmersivePresentation

end Algebra

namespace RingHom

/- Standard smoothness for a ring map is the ring-hom version of the same canonical notion. -/
@[stacks 00T6 "standard smooth ring-map predicate"]
#check @IsStandardSmooth

/- For an algebra map, ring-hom standard smoothness agrees with algebra standard smoothness. -/
@[stacks 00T6 "standard smooth algebra-map bridge"]
#check @isStandardSmooth_algebraMap

end RingHom
