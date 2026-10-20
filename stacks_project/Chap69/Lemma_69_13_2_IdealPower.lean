module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-! # Ideal-power products on algebraic spaces

The public owner contains the actual ideal action and recursive image-subobject powers.
The source lemma retains its original tagged statement in `Lemma_69_13_2`.
-/

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.idealPowerProductSubobject :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      (I : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X) (F : X.Modules) (n : ℕ),
      CategoryTheory.Subobject F)
