/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Affine permanence for morphisms of algebraic spaces

An affine composite of algebraic spaces may be cancelled when the second map
has affine or separated relative diagonal. Morphisms from affine algebraic
spaces to spaces with affine absolute diagonal or absolute separation are affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

/-- If a composite of morphisms of algebraic spaces is affine and the second
morphism has affine relative diagonal, then the first morphism is affine. -/
@[stacks 08GB]
theorem of_comp_of_affineDiagonal {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (g : X ⟶ Y) (f : Y ⟶ B) [Affine (g ≫ f)] [Affine (pullback.diagonal f)] :
    Affine g :=
  sorry

/-- If a composite of morphisms of algebraic spaces is affine and the second
morphism is separated, then the first morphism is affine. -/
@[stacks 08GB]
theorem of_comp {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (g : X ⟶ Y) (f : Y ⟶ B)
    [Affine (g ≫ f)] [Separated f] : Affine g :=
  sorry

/-- A morphism from an affine algebraic space to an algebraic space whose
diagonal over the terminal scheme is affine is affine. -/
@[stacks 08GB]
theorem of_isAffine_of_affineDiagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : X ⟶ Y) [IsAffine X]
    [Affine (prod.lift (𝟙 (extendBaseTerminal Y)) (𝟙 (extendBaseTerminal Y)))] :
    Affine g :=
  sorry

/-- A morphism from an affine algebraic space to an absolutely separated
algebraic space is affine. -/
@[stacks 08GB]
theorem of_isAffine_of_isAbsolutelySeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (g : X ⟶ Y) [IsAffine X] [IsAbsolutelySeparated Y] :
    Affine g :=
  sorry

end Affine

end AlgebraicGeometry.AlgebraicSpace
