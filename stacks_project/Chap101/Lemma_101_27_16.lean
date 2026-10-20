/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Descent
import StacksCheckRecall

/-!
# Descent of quasi-compact morphisms of algebraic stacks along fppf morphisms

Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of its base change along a surjective, flat, locally of
finite presentation morphism of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/- Lemma 101.27.16: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective, flat, locally of finite presentation morphism of
algebraic stacks. If the base change `TwoFibreProduct.snd f g` is quasi-compact,
then `f` is quasi-compact. -/
@[stacks 0DQK] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_surjective_flat_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [QuasiCompact (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    QuasiCompact f)

/- Quasi-compactness of a morphism of algebraic stacks follows from
quasi-compactness of the second projection of a bilimit `PseudoPullbackCone`
against a surjective, flat, locally of finite presentation morphism of
algebraic stacks. -/
#check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_isBilimit_surjective_flat_locallyOfFinitePresentation :
    ∀
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [QuasiCompact c.snd],
    QuasiCompact f)

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
