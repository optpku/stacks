/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
import StacksCheckRecall

@[expose] public section

universe u v w vB

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace

/- 79.1.0.1: the quotient-atlas square of a groupoid in algebraic spaces is
2-cartesian over the quotient stack `[U/R]`.

```text
R  ───▶ U
│       │
▼       ▼
U  ───▶ quotientStack
```
-/
@[stacks 04P6] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTargetCone_isBilimit :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTargetCone G).IsBilimit)
