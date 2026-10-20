/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Descent of local finite presentation for morphisms of algebraic stacks

Local finite presentation descends along surjective, flat morphisms that are
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- A morphism of algebraic stacks is locally of finite presentation if its
base change along a surjective, flat, locally of finite presentation morphism
is locally of finite presentation. -/
@[stacks 06Q8]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFinitePresentation f :=
  sorry

/-- Local finite presentation of a morphism of algebraic stacks follows from
local finite presentation of the second projection of a bilimit
`PseudoPullbackCone` against a surjective, flat, locally of finite presentation
morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFinitePresentation c.snd] :
    LocallyOfFinitePresentation f :=
  sorry

/-- After base change along a surjective, flat, locally of finite presentation
morphism of algebraic stacks, the original morphism is locally of finite
presentation if and only if `TwoFibreProduct.snd f g` is locally of finite
presentation. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔
      LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
