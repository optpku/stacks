/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder

/-!
# Conormal sheaves of local complete intersection morphisms of algebraic spaces

The relative conormal sheaf of a formally unramified local complete intersection
morphism, represented by any universal first-order thickening, is finite locally free.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- The conormal sheaf of any universal first-order thickening of a formally
unramified local complete intersection morphism of algebraic spaces is finite
locally free. -/
theorem conormalSheaf_isFiniteLocallyFree {S : Scheme.{u}}
    {X Y X' : AlgebraicSpace S} (i : X ⟶ X') (f : X' ⟶ Y)
    [FormallyUnramified (i ≫ f)] [IsLocalCompleteIntersection (i ≫ f)]
    [IsUniversalFirstOrder i f] : (Hom.conormalSheaf i).IsFiniteLocallyFree :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
