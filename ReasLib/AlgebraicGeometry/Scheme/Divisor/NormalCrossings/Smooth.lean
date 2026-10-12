/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsStrictNormalCrossingsDivisor

/-- Pullback along a smooth morphism preserves strict normal crossings divisors. -/
instance comap_smooth {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [IsStrictNormalCrossingsDivisor D]
    (f : Y ⟶ X) [Smooth f] :
    @IsStrictNormalCrossingsDivisor Y
      (LocallyOfFiniteType.isLocallyNoetherian f) (D.comap f) := sorry

end AlgebraicGeometry.IsStrictNormalCrossingsDivisor

namespace AlgebraicGeometry.IsNormalCrossingsDivisor

/-- Pullback along a smooth morphism preserves normal crossings divisors. -/
instance comap_smooth {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) [IsNormalCrossingsDivisor D]
    (f : Y ⟶ X) [Smooth f] :
    @IsNormalCrossingsDivisor Y
      (LocallyOfFiniteType.isLocallyNoetherian f) (D.comap f) := sorry

end AlgebraicGeometry.IsNormalCrossingsDivisor
