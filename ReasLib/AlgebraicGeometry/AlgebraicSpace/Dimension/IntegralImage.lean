/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IntegralImage

/-!
# Dimensions of integral images

The integral image of an integral closed subspace under a proper morphism over
a universally catenary base has no greater relative dimension than the subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The `δ`-dimension of the integral image of an integral closed subspace along
a proper morphism over `B` is at most the `δ`-dimension of the source subspace. -/
theorem closedSubspaceDeltaDimension_integralImage_le
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) [IsDecent Y]
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension pY δ (Z.integralImage f) ≤
      AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension pX δ Z :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
