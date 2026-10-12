/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 66.25.4: a regular algebraic space is normal. -/
@[stacks 0BGT] #check (AlgebraicGeometry.AlgebraicSpace.IsRegular.instIsNormal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsRegular X],
    AlgebraicGeometry.AlgebraicSpace.IsNormal X)
