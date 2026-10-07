module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

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

/-- Lemma 101.3.6: Let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the following are equivalent: `f` is
quasi-separated, `Hom.diagonal f` is quasi-compact, or `Hom.diagonal f` is of
finite type. -/
@[stacks 04YT]
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
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated on scheme-slice tests if and only if its relative 2-diagonal is
of finite type. -/
theorem has_quasiSeparated_iff_finiteType_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiSeparated S) f ↔
      has (@AlgebraicSpace.FiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
