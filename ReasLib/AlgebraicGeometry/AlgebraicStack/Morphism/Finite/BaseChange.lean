/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Base change of integral and finite morphisms of algebraic stacks

Integral and finite morphisms of algebraic stacks are stable under base change,
both for arbitrary bilimit cones and for the canonical 2-fibre-product projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsIntegralHom

/-- Integral morphisms of algebraic stacks remain integral along the first
projection of any bilimit `PseudoPullbackCone` of an arbitrary morphism against
an integral morphism. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [IsIntegralHom g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsIntegralHom c.fst :=
  sorry

/-- The first projection of a chosen 2-fibre product is integral whenever the
second leg is an integral morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom g] :
    IsIntegralHom (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The second projection of a chosen 2-fibre product is integral whenever the
first leg is an integral morphism of algebraic stacks. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom f] :
    IsIntegralHom (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsIntegralHom

namespace AlgebraicGeometry.AlgebraicStack.IsFinite

/-- Finite morphisms of algebraic stacks remain finite along the first
projection of any bilimit `PseudoPullbackCone` of an arbitrary morphism against
a finite morphism. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [IsFinite g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsFinite c.fst :=
  sorry

/-- The first projection of a chosen 2-fibre product is finite whenever the
second leg is a finite morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite g] :
    IsFinite (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The second projection of a chosen 2-fibre product is finite whenever the
first leg is a finite morphism of algebraic stacks. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite f] :
    IsFinite (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsFinite
