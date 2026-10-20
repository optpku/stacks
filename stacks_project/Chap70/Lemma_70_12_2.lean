module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.ProperNoetherianApproximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.12.2: a proper morphism `f : X ⟶ Y` of algebraic spaces over
`Spec ℤ`, with `Y` quasi-compact and quasi-separated, is a directed inverse
limit of morphisms `f_i : X_i ⟶ Y_i` that are proper and of finite
presentation, with affine transitions on both systems, and with each `Y_i` of
finite presentation over `ℤ`. -/
@[stacks 0A0X] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_properNoetherianApproximation :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
      [Proper f] [IsQuasiCompact Y] [IsQuasiSeparated Y],
      Nonempty (ProperNoetherianApproximation f))
