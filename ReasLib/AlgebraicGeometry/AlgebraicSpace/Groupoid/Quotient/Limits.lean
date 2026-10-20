/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Equalizers in quotient stacks

The total category of the quotient stack of a groupoid in algebraic spaces
has equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The total category of the quotient stack of a groupoid in algebraic spaces
over `S` has equalizers. -/
@[stacks 06WY]
theorem hasEqualizers_quotientStack {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    HasEqualizers (GroupoidAlgebraicSpace.SmallQuotient.quotientStack G).total := sorry

end AlgebraicGeometry.GroupoidsOver
