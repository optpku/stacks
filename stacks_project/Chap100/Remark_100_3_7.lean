/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SpacesOver
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.LocallyGroupoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Remark 100.3.7: the hom-categories of `SpacesOver Y` are thin:
2-morphisms between parallel 1-morphisms are unique when they exist, by
faithfulness of the target structural morphism. -/
@[stacks 04ZQ] #check
  (AlgebraicGeometry.SpacesOver.homIsThin :
    ∀ {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
      (P Q : AlgebraicGeometry.SpacesOver Y), Quiver.IsThin (P ⟶ Q))

/- The objects are morphisms `f : X ⟶ Y` of algebraic stacks representable by
algebraic spaces. A 1-morphism consists of `(g, β : f1 ≅ g ≫ f2)`; a 2-morphism
`α : g ⟶ g'` satisfies `β ≫ (α ▷ f2) = β'`. -/
#check (AlgebraicGeometry.SpacesOver :
  ∀ {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y], Type (u + 2))

/- Every 2-morphism is invertible, so the thin hom-categories are setoids. -/
#check (AlgebraicGeometry.SpacesOver.locallyGroupoid :
  ∀ {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y],
    CategoryTheory.Bicategory.IsLocallyGroupoid (AlgebraicGeometry.SpacesOver Y))

variable {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y]

/- Replacing 1-morphisms by isomorphism classes yields the homotopy 1-category. -/
#check (CategoryTheory.Bicategory.HomotopyCategory (AlgebraicGeometry.SpacesOver Y) :
  Type (u + 2))
#check (CategoryTheory.Bicategory.HomotopyCategory.category
  (AlgebraicGeometry.SpacesOver Y) : CategoryTheory.Cat.{u + 1, u + 2})
#check (CategoryTheory.Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic :
  ∀ {P Q : AlgebraicGeometry.SpacesOver Y} {f g : P ⟶ Q},
    CategoryTheory.Bicategory.HomotopyCategory.mkHom f =
        CategoryTheory.Bicategory.HomotopyCategory.mkHom g ↔
      CategoryTheory.IsIsomorphic f g)
