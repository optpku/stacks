/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.Section.fiberComponent :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) → (s : Y ⟶ X) →
    s ≫ f = 𝟙 Y → Y → Set X)

#check (AlgebraicGeometry.Scheme.Hom.Section.componentLocus :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) → (s : Y ⟶ X) →
    s ≫ f = 𝟙 Y → Set X)
