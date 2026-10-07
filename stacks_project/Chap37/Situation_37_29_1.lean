module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent

open CategoryTheory

universe u

/- Situation 37.29.1: given a section `s` of `f`, `componentLocus f s hs` is the union in `X`
of the connected components of the fibres of `f` that contain the points selected by `s`. -/
@[stacks 055L] #check (AlgebraicGeometry.Scheme.Hom.Section.componentLocus :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) → (s : Y ⟶ X) →
    s ≫ f = 𝟙 Y → Set X)

/- For each `y : Y`, this is the connected component of the fibre over `y`
that contains the point selected by the section. -/
#check (AlgebraicGeometry.Scheme.Hom.Section.fiberComponent :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) → (s : Y ⟶ X) →
    s ≫ f = 𝟙 Y → Y → Set X)
