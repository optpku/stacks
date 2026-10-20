/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target of a finite surjective morphism of algebraic spaces from an
affine algebraic space is affine if the target is Noetherian. -/
theorem isAffine_of_isFinite_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X] : IsAffine X :=
  sorry

/-- The target of a finite surjective morphism of algebraic spaces from an
affine algebraic space is affine. -/
theorem IsAffine.of_isFinite_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [IsFinite f] [IsAffine X] : IsAffine Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
