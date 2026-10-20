/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
public import stacks_project.Chap101.Lemma_101_15_1_Homeomorph

/-!
# Universal homeomorphisms of algebraic stacks

The universal-homeomorphism class and its companion results are owned by the
shared algebraic-stack module. The historical homeomorphism import preserves
the point-cone and comparison API.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    UniversalHomeomorphism (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversalHomeomorphism f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → pointsIsHomeomorph snd)

#check (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversalHomeomorphism f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check (AlgebraicGeometry.AlgebraicStack.pointsIsHomeomorph_of_universalHomeomorphism :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [UniversalHomeomorphism f],
    pointsIsHomeomorph f)

#check (AlgebraicGeometry.AlgebraicStack.universalHomeomorphism_iff_pointsIsHomeomorph_of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    UniversalHomeomorphism f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → pointsIsHomeomorph snd)

#check (AlgebraicGeometry.AlgebraicStack.universalHomeomorphism_iff_twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    UniversalHomeomorphism f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
