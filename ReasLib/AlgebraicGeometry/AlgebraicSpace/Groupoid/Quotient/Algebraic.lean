/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Algebraicity of smooth groupoid quotients

The quotient stack of a smooth groupoid in algebraic spaces is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The quotient stack of a smooth groupoid in algebraic spaces over an algebraic
space over a scheme `S` is an algebraic stack over `S`. -/
theorem instAlgebraicStack_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    AlgebraicStack (SmallQuotient.quotientStack G) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
