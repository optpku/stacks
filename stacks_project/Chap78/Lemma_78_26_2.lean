/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Square
import StacksCheckRecall

universe u

/- Lemma 78.26.2: The stack of points of the stabilizer is the canonical two-fibre product
of the inertia of the quotient stack and the stack of points of the object space over the
quotient stack. -/
@[stacks 06PC] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.inertiaCone_isBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      (AlgebraicGeometry.GroupoidAlgebraicSpace.inertiaCone G).IsBilimit)
