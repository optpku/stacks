module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Quasi-separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated in the scheme-slice sense of algebraic spaces if and only if
its relative 2-diagonal is quasi-compact, equivalently of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For a morphism of algebraic stacks representable by algebraic spaces,
quasi-separatedness, quasi-compactness of its relative 2-diagonal, and finite
type of its relative 2-diagonal are equivalent. -/
theorem quasiSeparated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    List.TFAE
      [has (@AlgebraicSpace.QuasiSeparated S) f,
        has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.FiniteType S)
          (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated on scheme-slice tests if and only if its relative 2-diagonal is
quasi-compact. -/
theorem has_quasiSeparated_iff_quasiCompact_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiSeparated S) f ↔
      has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (quasiSeparated_tfae hf).out 0 1

/-- A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated on scheme-slice tests if and only if its relative 2-diagonal is
of finite type. -/
theorem has_quasiSeparated_iff_finiteType_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiSeparated S) f ↔
      has (@AlgebraicSpace.FiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (quasiSeparated_tfae hf).out 0 2

end AlgebraicGeometry.Groupoids.Hom
