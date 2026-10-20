/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Pullback
import StacksCheckRecall

/-!
# Base change of separation axioms for morphisms of algebraic stacks

Each separation axiom is stable under 2-fibre-product base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.4.4: The base change of a DM morphism of algebraic stacks
along any morphism of algebraic stacks is DM. -/
@[stacks 050F] #check (AlgebraicGeometry.AlgebraicStack.DM.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.DM f],
    AlgebraicStack.DM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/- Lemma 101.4.4: The base change of a quasi-DM morphism of algebraic stacks
along any morphism of algebraic stacks is quasi-DM. -/
@[stacks 050F] #check (AlgebraicGeometry.AlgebraicStack.QuasiDM.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.QuasiDM f],
    AlgebraicStack.QuasiDM (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/- Lemma 101.4.4: The base change of a separated morphism of algebraic stacks
along any morphism of algebraic stacks is separated. -/
@[stacks 050F] #check (AlgebraicGeometry.AlgebraicStack.Separated.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.Separated f],
    AlgebraicStack.Separated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/- Lemma 101.4.4: The base change of a quasi-separated morphism of algebraic stacks
along any morphism of algebraic stacks is quasi-separated. -/
@[stacks 050F] #check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.QuasiSeparated f],
    AlgebraicStack.QuasiSeparated (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
