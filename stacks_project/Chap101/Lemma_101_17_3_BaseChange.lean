/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_37_1_FiniteType

/-!
# Base change of finite type morphisms of algebraic stacks

Finite type and locally of finite type morphisms of algebraic stacks remain
so along the second projection of any bilimit 2-fibre product cone, and along
the first projection of a chosen 2-fibre product when that leg has the
corresponding property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FiniteType

/-- Finite type morphisms of algebraic stacks remain of finite type along the
second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [FiniteType f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    FiniteType c.snd := sorry

/-- The first projection of a chosen 2-fibre product is of finite type whenever
the second leg is a finite type morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [FiniteType g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    FiniteType (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.FiniteType

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Locally of finite type morphisms of algebraic stacks remain locally of
finite type along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [LocallyOfFiniteType f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    LocallyOfFiniteType c.snd := sorry

/-- The first projection of a chosen 2-fibre product is locally of finite type
whenever the second leg is a locally of finite type morphism of algebraic
stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFiniteType (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
