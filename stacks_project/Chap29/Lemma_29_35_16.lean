/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Cancellation
import StacksCheckRecall

/-!
# Lemma 29.35.16

Unramifiedness of a composite descends to its left factor.

@stack 02GG
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/- Lemma 29.35.16 (1): if `X` is unramified over `S`, then `f : X ⟶ Y` is unramified. -/
@[stacks 02GG]
#check (AlgebraicGeometry.Unramified.of_comp :
  ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [Unramified (f ≫ g)], Unramified f)

/- Lemma 29.35.16 (2): if `X` is G-unramified over `S` and `Y` is locally of finite type over
`S`, then `f : X ⟶ Y` is G-unramified. -/
@[stacks 02GG]
#check (AlgebraicGeometry.GUnramified.of_comp :
  ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [GUnramified (f ≫ g)]
    [LocallyOfFiniteType g], GUnramified f)

end AlgebraicGeometry
