/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.4.12 (1): if `f ≫ g` is DM then so is `f`. -/
@[stacks 050M] #check
  (AlgebraicGeometry.AlgebraicStack.DM.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [DM (f ≫ g)],
      DM f)

/- Lemma 101.4.12 (2): if `f ≫ g` is quasi-DM then so is `f`. -/
@[stacks 050M] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiDM.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiDM (f ≫ g)],
      QuasiDM f)

/- Lemma 101.4.12 (3): if `f ≫ g` is separated and `Hom.diagonal g` is
separated, then `f` is separated. -/
@[stacks 050M] #check
  (AlgebraicGeometry.AlgebraicStack.Separated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Separated (f ≫ g)],
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (Hom.diagonal.{u + 1, u, u + 1} g) →
        Separated f)

/- Lemma 101.4.12 (4): if `f ≫ g` is quasi-separated and `Hom.diagonal g` is
quasi-separated, then `f` is quasi-separated. -/
@[stacks 050M] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiSeparated (f ≫ g)],
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} g) →
        QuasiSeparated f)
