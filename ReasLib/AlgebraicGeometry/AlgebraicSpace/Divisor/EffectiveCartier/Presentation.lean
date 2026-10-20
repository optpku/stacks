/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Presentations of invertible modules by effective Cartier divisors

Every invertible module on a regular Noetherian absolutely separated algebraic
space is isomorphic to the difference sheaf of two effective Cartier divisors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every invertible module on a regular Noetherian absolutely separated algebraic
space is isomorphic to the difference sheaf of two effective Cartier divisors. -/
theorem exists_iso_differenceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
    (L : X.Modules) [isInvertibleObject L] :
    ∃ (D : ClosedSubspace X) (hD : IsEffectiveCartierDivisor D.ι)
      (D' : ClosedSubspace X) (hD' : IsEffectiveCartierDivisor D'.ι),
      Nonempty (L ≅ @ClosedSubspace.differenceSheaf S X D D' hD hD') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
