/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches

/-!
# Existence and comparison of versal rings

Finite-type field-valued points of locally finite type algebraic stacks over
locally Noetherian schemes admit versal rings. Any two such rings differ by a
finite-variable power-series extension in one direction or the other.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A finite-type field-valued point of a locally finite type algebraic stack
over a locally Noetherian scheme admits a versal ring. -/
theorem exists_isVersalRing {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    ∃ A : CompleteLocalSAlgebra S, IsVersalRing x0 A :=
  sorry

/-- Any two versal rings at the same finite-type field-valued point of a
locally finite type algebraic stack over a locally Noetherian scheme differ
by a finite-variable power-series extension over the base scheme in one
direction or the other. -/
theorem exists_isPowerSeriesExtension_or {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A'] :
    (∃ φ : CompleteLocalSAlgebra.Hom A A', IsPowerSeriesExtension φ) ∨
      ∃ φ : CompleteLocalSAlgebra.Hom A' A, IsPowerSeriesExtension φ :=
  sorry

end AlgebraicGeometry.AlgebraicStack
