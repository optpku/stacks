/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Pullback

/-- The fibre product of affine schemes over a separated scheme is affine. -/
instance isAffine_of_isSeparated
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] [S.IsSeparated] : IsAffine (pullback f g) :=
  sorry

end Scheme.Pullback

end AlgebraicGeometry
