/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-separated morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is quasi-separated when its relative
2-diagonal is representable by algebraic spaces and both quasi-compact and
quasi-separated on scheme-slice representing morphisms. -/
class QuasiSeparated {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is representable by algebraic spaces. -/
  representable_diagonal :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f)
  /-- The relative 2-diagonal is quasi-compact. -/
  quasiCompact_diagonal : has (@AlgebraicSpace.QuasiCompact S) (diagonal f)
  /-- The relative 2-diagonal is quasi-separated. -/
  quasiSeparated_diagonal : has (@AlgebraicSpace.QuasiSeparated S) (diagonal f)

namespace QuasiSeparated

/-- The identity 1-morphism of a category fibred in groupoids is
quasi-separated. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    QuasiSeparated (𝟙 X) := sorry

/-- A 1-morphism is quasi-separated if and only if its relative 2-diagonal is
representable by algebraic spaces and both quasi-compact and quasi-separated. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    QuasiSeparated f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
        has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
          has (@AlgebraicSpace.QuasiSeparated S) (diagonal f) := sorry

/-- The relative 2-diagonal of a quasi-separated 1-morphism is representable by
algebraic spaces and both quasi-compact and quasi-separated. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [QuasiSeparated f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
      has (@AlgebraicSpace.QuasiCompact S) (diagonal f) ∧
        has (@AlgebraicSpace.QuasiSeparated S) (diagonal f) := sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
