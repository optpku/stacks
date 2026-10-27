/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.UniversallyClosed

/-!
# Proper morphisms of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open AlgebraicGeometry.AlgebraicSpace.CohStack (AlgebraicStack)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of algebraic stacks over `S`, in the Hom-universe of
`CohStack.toGroupoids`, is proper if it is separated, of finite type, and
universally closed. -/
@[mk_iff]
class Proper {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Separated f, FiniteType f, UniversallyClosed f

namespace Proper

/-- A proper 1-morphism of algebraic stacks is separated, of finite type, and
universally closed. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Proper f] :
    Separated f ∧ FiniteType f ∧ UniversallyClosed f :=
  sorry

/-- The identity 1-morphism of an algebraic stack is proper. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : Proper (𝟙 X) :=
  sorry

/-- A separated, finite type, and universally closed 1-morphism of algebraic
stacks is proper. -/
instance instOfSeparatedFiniteTypeUniversallyClosed {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Separated f] [FiniteType f] [UniversallyClosed f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
