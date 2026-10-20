module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap94.Definition_94_12_1_Representable

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
/-!
# Formal smoothness on objects for groupoid fibrations

The formal-smoothness property and its commuting-square characterization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.restrictionSquare_commSq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    {U U' : Over S} (i : U ⟶ U')
    {x' : GroupoidsOver.slice U' ⟶ X} {y' : GroupoidsOver.slice U' ⟶ Y}
    {x : GroupoidsOver.slice U ⟶ X} (β : slice.pullback i x' ≅ x)
    (γ : x ≫ p ≅ slice.pullback i y') (γ' : x' ≫ p ≅ y'),
    AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.restrictionSquare p i β γ γ' ↔
      CommSq (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.restrictHom p i γ')
        (β.hom ▷ p) (𝟙 (slice.pullback i y')) γ.hom)
