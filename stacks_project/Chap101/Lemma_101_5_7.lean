/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Presentation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 101.5.7: For an algebraic stack with a presentation, the canonical square from
its stabilizer algebraic space to the presentation object space and from its inertia
stack to the stack is a fibre product. -/
@[stacks 06PR] #check
  (AlgebraicGeometry.AlgebraicStack.Inertia.presentationInertiaCone_isBilimit :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (P : Presentation X),
      (AlgebraicGeometry.AlgebraicStack.Inertia.presentationInertiaCone P).IsBilimit)
