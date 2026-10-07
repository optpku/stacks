module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.Smooth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.21.3: the pullback of a strict normal crossings divisor along a smooth morphism
is a strict normal crossings divisor. -/
@[stacks 0CBP] #check
  (AlgebraicGeometry.IsStrictNormalCrossingsDivisor.comap_smooth :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X]
      (D : X.IdealSheafData) [IsStrictNormalCrossingsDivisor D]
      (f : Y ⟶ X) [Smooth f],
      @IsStrictNormalCrossingsDivisor Y
        (LocallyOfFiniteType.isLocallyNoetherian f) (D.comap f))
