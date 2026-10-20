/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.FiniteType
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Diagonals of representable morphisms of algebraic stacks

If a morphism of algebraic stacks is representable by algebraic spaces, then
its relative 2-diagonal is representable by schemes, a monomorphism, separated,
and locally quasi-finite in the scheme-slice sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

namespace Mono

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is a monomorphism in the scheme-slice sense. -/
instance diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    let _ := hf
    Mono (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end Mono

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is separated on scheme-slice tests. -/
theorem has_separated_diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is locally quasi-finite on scheme-slice tests. -/
theorem has_locallyQuasiFinite_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallyQuasiFinite S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
