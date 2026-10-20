module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.RelativeNoetherianApproximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.10.1: a morphism of quasi-compact and quasi-separated algebraic
spaces over `Spec ℤ` is a directed inverse limit of morphisms of
quasi-separated algebraic spaces of finite type over `ℤ` with affine
transition morphisms. -/
@[stacks 0GS3] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_relativeNoetherianApproximation :
    ∀ {X Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsQuasiSeparated X]
      [IsQuasiCompact Y] [IsQuasiSeparated Y],
      Nonempty (RelativeNoetherianApproximation f))
