/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.QuasiSeparated
import StacksCheckRecall

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

/- Lemma 101.3.6: Let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the following are equivalent: `f` is
quasi-separated, `Hom.diagonal f` is quasi-compact, or `Hom.diagonal f` is of
finite type. -/
@[stacks 04YT] #check (AlgebraicGeometry.Groupoids.Hom.quasiSeparated_tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    List.TFAE
      [has (@AlgebraicSpace.QuasiSeparated S) f,
        has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.FiniteType S)
          (Hom.diagonal.{u + 1, u, u + 1} f)])

/- A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated on scheme-slice tests if and only if its relative 2-diagonal is
quasi-compact. -/
#check (AlgebraicGeometry.Groupoids.Hom.has_quasiSeparated_iff_quasiCompact_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    has (@AlgebraicSpace.QuasiSeparated S) f ↔
      has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} f))

/- A morphism of algebraic stacks representable by algebraic spaces is
quasi-separated on scheme-slice tests if and only if its relative 2-diagonal is
of finite type. -/
#check (AlgebraicGeometry.Groupoids.Hom.has_quasiSeparated_iff_finiteType_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    has (@AlgebraicSpace.QuasiSeparated S) f ↔
      has (@AlgebraicSpace.FiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} f))

end AlgebraicGeometry.Groupoids.Hom
