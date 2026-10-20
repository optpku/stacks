module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Derived

/-! # Square-zero algebra extensions and their derived coefficient map -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension.trivial :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (ℱ : X.Modules),
    SquareZeroAlgebraExtension f ℱ)
