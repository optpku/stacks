/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Descent of quasi-compact morphisms of algebraic stacks

Quasi-compactness descends along surjective, flat, locally of finite
presentation morphisms of algebraic stacks, including coverings from
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- A morphism of algebraic stacks is quasi-compact if its base change along
a surjective, flat, locally of finite presentation morphism from an algebraic
space is quasi-compact. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [QuasiCompact (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    QuasiCompact f :=
  sorry

/-- Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of the second projection of a bilimit `PseudoPullbackCone`
against a surjective, flat, locally of finite presentation morphism from an
algebraic space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiCompact c.snd] :
    QuasiCompact f :=
  sorry

/-- A morphism of algebraic stacks is quasi-compact if its base change along
a surjective, flat, locally of finite presentation morphism of algebraic
stacks is quasi-compact. -/
theorem of_surjective_flat_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [QuasiCompact (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    QuasiCompact f :=
  sorry

/-- Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of the second projection of a bilimit `PseudoPullbackCone`
against a surjective, flat, locally of finite presentation morphism of
algebraic stacks. -/
theorem of_isBilimit_surjective_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiCompact c.snd] :
    QuasiCompact f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
