module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Scheme-theoretic fibres of algebraic spaces over scheme points

The scheme-theoretic fibre of a morphism of algebraic spaces over a scheme `Y` at a point
`y` is the fibre product against `Spec(κ(y)) → Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `Y` represented by `Spec(κ(y))`. -/
def residueFieldSpace {Y : Scheme.{u}} (y : Y) : AlgebraicSpace Y :=
  ofOver (Over.mk (Y.fromSpecResidueField y))

/-- `residueFieldSpace y` is `ofOver` of the residue-field morphism at `y`. -/
theorem residueFieldSpace_eq {Y : Scheme.{u}} (y : Y) :
    residueFieldSpace y = ofOver (Over.mk (Y.fromSpecResidueField y)) :=
  rfl

/-- The morphism `Spec(κ(y)) → Y` as a morphism of algebraic spaces over `Y`. -/
def residueFieldHom (Y : Scheme.{u}) (y : Y) :
    residueFieldSpace y ⟶ ofOver (Over.mk (𝟙 Y)) :=
  ofOverHomMk (Y.fromSpecResidueField y) (Category.comp_id _)

/-- `residueFieldHom Y y` is `ofOverHomMk` of `Y.fromSpecResidueField y`. -/
theorem residueFieldHom_eq (Y : Scheme.{u}) (y : Y) :
    residueFieldHom Y y =
      ofOverHomMk (Y.fromSpecResidueField y) (Category.comp_id _) :=
  rfl

/-- The scheme-theoretic fibre of a morphism of algebraic spaces over `Y` at a point `y`. -/
def fiber {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) : AlgebraicSpace Y :=
  pullback f (residueFieldHom Y y)

/-- `fiber f y` is the fibre product of `f` against `residueFieldHom Y y`. -/
theorem fiber_eq_pullback {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) :
    fiber f y = pullback f (residueFieldHom Y y) :=
  rfl

/-- The canonical projection from the scheme-theoretic fibre to the source. -/
def fiberι {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) :
    fiber f y ⟶ X :=
  pullback.fst f (residueFieldHom Y y)

/-- `fiberι f y` is the first projection of the fibre product. -/
theorem fiberι_eq {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) :
    fiberι f y = pullback.fst f (residueFieldHom Y y) :=
  rfl

/-- The structure morphism of the scheme-theoretic fibre to `Spec(κ(y))`. -/
def fiberToSpec {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) :
    fiber f y ⟶ residueFieldSpace y :=
  pullback.snd f (residueFieldHom Y y)

/-- `fiberToSpec f y` is the second projection of the fibre product. -/
theorem fiberToSpec_eq {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) :
    fiberToSpec f y = pullback.snd f (residueFieldHom Y y) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
