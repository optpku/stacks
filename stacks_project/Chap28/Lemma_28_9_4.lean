/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Regular
import StacksCheckRecall

@[expose] public section

universe u

/-
Lemma 28.9.4: A regular scheme is normal.
-/
@[stacks 0569] #check
  (AlgebraicGeometry.Scheme.Regular.isNormal :
    {X : AlgebraicGeometry.Scheme.{u}} →
      AlgebraicGeometry.Scheme.Regular X → AlgebraicGeometry.Scheme.isNormal X)

end
