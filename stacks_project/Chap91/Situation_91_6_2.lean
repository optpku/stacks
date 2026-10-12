/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.SesFlat
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

universe u

/- Situation 91.6.2

A morphism `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` of ringed spaces together with a
commutative diagram of first-order thickenings whose top row is a short exact
sequence of first-order thickenings of `X`, whose bottom row is a short exact
sequence of first-order thickenings of `S`, each `f'_i` restricts to `f`, each
pair `(f, f'_i)` is a strict morphism of thickenings, and each `f'_i` is flat,
together with an `𝒪'_2`-module `F'_2` flat over `S'_2` with `F = F'_2|_X` and
the canonical splitting `π : X'_1 ⟶ X` from Remark 91.4.9. -/
@[stacks 08VS] #check
  (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.SesFlatThickenings :
    {X S X1 X2 X3 S1 S2 S3 : AlgebraicGeometry.RingedSpace.{u}} →
      (f : X ⟶ S) → (i1 : X ⟶ X1) → (i2 : X ⟶ X2) → (i3 : X ⟶ X3) →
      (t1 : S ⟶ S1) → (t2 : S ⟶ S2) → (t3 : S ⟶ S3) →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i1] →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i2] →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i3] →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t1] →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t2] →
      [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t3] → Type (u + 1))

#check @SesFlatThickenings.canonicalSplitting
#check @SesFlatThickenings.moduleRestrict
#check @SesFlatThickenings.of
