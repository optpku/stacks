module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Restriction of algebraic-space sections to the function field
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `W` induced by
`W.fromSpecStalk (genericPoint W)`. -/
def genericPointHom (W : Scheme.{u}) [IsIntegral W] :
    ofOver (Over.mk (W.fromSpecStalk (genericPoint W))) ⟶
      ofOver (Over.mk (𝟙 W)) :=
  ofOverHomMk (W.fromSpecStalk (genericPoint W))
    (Category.comp_id (W.fromSpecStalk (genericPoint W)))

/-- Unfolding `genericPointHom` recovers `ofOverHomMk` of
`W.fromSpecStalk (genericPoint W)`. -/
theorem genericPointHom_eq (W : Scheme.{u}) [IsIntegral W] :
    genericPointHom W =
      ofOverHomMk (W.fromSpecStalk (genericPoint W))
        (Category.comp_id (W.fromSpecStalk (genericPoint W))) :=
  rfl

/-- The generic point of an integral scheme `W`, as a morphism in the slice of
algebraic spaces over `ofOver (Over.mk (𝟙 W))`. -/
def genericPointOver (W : Scheme.{u}) [IsIntegral W] :
    Over.mk (genericPointHom W) ⟶
      Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) :=
  Over.homMk (genericPointHom W)

/-- `genericPointOver W` is the slice morphism associated to
`genericPointHom W`. -/
theorem genericPointOver_eq (W : Scheme.{u}) [IsIntegral W] :
    genericPointOver W = Over.homMk (genericPointHom W) :=
  rfl

/-- Restriction of sections of an algebraic space `Y` over `W` along
`W.fromSpecStalk (genericPoint W)`, as precomposition in the slice over
`ofOver (Over.mk (𝟙 W))`. -/
def sectionsRestrictFunctionField {W : Scheme.{u}} [IsIntegral W]
    (Y : Over (ofOver (Over.mk (𝟙 W)))) :
    (Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) ⟶ Y) →
      (Over.mk (genericPointHom W) ⟶ Y) :=
  fun s ↦ genericPointOver W ≫ s

/-- Unfolding `sectionsRestrictFunctionField` recovers precomposition with
`Over.homMk (genericPointHom W)`. -/
theorem sectionsRestrictFunctionField_apply {W : Scheme.{u}} [IsIntegral W]
    {Y : Over (ofOver (Over.mk (𝟙 W)))}
    (s : Over.mk (𝟙 (ofOver (Over.mk (𝟙 W)))) ⟶ Y) :
    sectionsRestrictFunctionField Y s =
      Over.homMk (genericPointHom W) ≫ s :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
