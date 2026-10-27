/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFiniteType

/-!
# Finite type morphisms of lifted groupoid fibrations
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
`CohStack.toGroupoids`, is of finite type if it is quasi-compact and locally of
finite type. -/
@[mk_iff]
class FiniteType {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends QuasiCompact f, LocallyOfFiniteType f

namespace FiniteType

/-- A finite-type 1-morphism of algebraic stacks is quasi-compact and locally of
finite type. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FiniteType f] :
    QuasiCompact f ∧ LocallyOfFiniteType f :=
  sorry

/-- The identity 1-morphism of an algebraic stack is of finite type. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] : FiniteType (𝟙 X) :=
  sorry

/-- A quasi-compact 1-morphism that is locally of finite type is of finite
type. -/
instance instOfQuasiCompactLocallyOfFiniteType {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFiniteType f] : FiniteType f :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
