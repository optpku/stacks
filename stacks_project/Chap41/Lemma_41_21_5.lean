/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.Smooth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.21.5: if `D` is a normal crossings divisor on a locally Noetherian scheme `X`,
then `D.comap f` is a normal crossings divisor for every smooth morphism `f : Y ⟶ X`. -/
@[stacks 0CBQ] #check
  (AlgebraicGeometry.IsNormalCrossingsDivisor.comap_smooth :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X]
      (D : X.IdealSheafData) [IsNormalCrossingsDivisor D]
      (f : Y ⟶ X) [Smooth f],
      @IsNormalCrossingsDivisor Y
        (LocallyOfFiniteType.isLocallyNoetherian f) (D.comap f))
