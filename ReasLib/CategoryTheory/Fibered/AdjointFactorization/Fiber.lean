/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Projections

/-!
# Fibers of the target leg in the adjoint factorization

The adjoint factorization of `F : X ⟶ Y` has a target leg
`AdjointFactorization.toTarget F : AdjointFactorization.middle F ⟶ Y`.  Its underlying functor is
itself fibred, so it canonically defines a fibred category over the total category `Y.total`.

This file owns that second fibred-category view and its fibers.  It also exposes the source endpoint
as a functor on each fiber.  Applications such as fiberwise Kan extensions or category homology can
therefore use the construction without rebuilding an instance for the target projection or
unfolding the vertical comma category.
-/

@[expose] public section

open CategoryTheory

universe u v w uD vD

namespace CategoryTheory.FiberedCategoryOver.AdjointFactorization

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}

noncomputable section

/-- The underlying target projection in the adjoint factorization of `F`. -/
abbrev targetProjection (F : X ⟶ Y) : (middle F).total ⥤ Y.total :=
  toFunctor (toTarget F)

/-- The intermediate category, regarded as a fibred category over `Y.total` through the target
projection.  This is the canonical owner for families of comparison-index categories. -/
def overTarget (F : X ⟶ Y) : FiberedCategoryOver Y.total :=
  FiberedCategoryOver.ofFunctor (targetProjection F)

/-- The projection of `overTarget F` is the target leg of the adjoint factorization. -/
@[simp]
theorem overTarget_p (F : X ⟶ Y) :
    (overTarget F).p = targetProjection F := sorry

/-- The fiber of the target leg over `y`; its objects are vertical arrows
`y ⟶ F(x)`, with equality to `y` recorded by the canonical `Functor.Fiber` owner. -/
abbrev targetFiber (F : X ⟶ Y) (y : Y.total) :=
  (overTarget F).p.Fiber y

/-- The source endpoint functor from the target-based factorization category to `X.total`. -/
def source (F : X ⟶ Y) : (overTarget F).total ⥤ X.total :=
  toFunctor (toSource F)

/-- On objects, the source endpoint functor selects the right endpoint of the vertical comma
arrow. -/
@[simp]
theorem source_obj (F : X ⟶ Y) (P : (overTarget F).total) :
    (source F).obj P = P.obj.right := sorry

/-- On morphisms, the source endpoint functor selects the right component of the comma square. -/
@[simp]
theorem source_map (F : X ⟶ Y) {P Q : (overTarget F).total} (φ : P ⟶ Q) :
    (source F).map φ = φ.hom.right := sorry

/-- The source endpoint functor restricted to the target fiber over `y`. -/
def fiberSource (F : X ⟶ Y) (y : Y.total) : targetFiber F y ⥤ X.total :=
  Functor.Fiber.fiberInclusion ⋙ source F

/-- The vertical comma object underlying an object of a target fiber. -/
abbrev fiberObject (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) :
    VerticalComma F :=
  P.1

/-- The left endpoint of a comparison object in the target fiber. -/
abbrev fiberLeft (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) : Y.total :=
  (fiberObject F P).obj.left

/-- The right endpoint of a comparison object in the target fiber. -/
abbrev fiberRight (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) : X.total :=
  (fiberObject F P).obj.right

/-- The vertical comparison arrow carried by an object of the target fiber. -/
abbrev fiberComparison (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) :
    fiberLeft F P ⟶ (toFunctor F).obj (fiberRight F P) :=
  (fiberObject F P).obj.hom

/-- The left endpoint of an object in the fiber over `y` is `y`. -/
theorem fiberLeft_eq (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) :
    fiberLeft F P = y := sorry

/-- Restricting the source endpoint functor to a target fiber sends an object to its right
endpoint. -/
@[simp]
theorem fiberSource_obj (F : X ⟶ Y) {y : Y.total} (P : targetFiber F y) :
    (fiberSource F y).obj P = fiberRight F P := sorry

/-- The comma square underlying a morphism in a target fiber. -/
abbrev fiberMap (F : X ⟶ Y) {y : Y.total} {P Q : targetFiber F y} (φ : P ⟶ Q) :
    fiberObject F P ⟶ fiberObject F Q :=
  φ.1

/-- The left component of a morphism in a target fiber. -/
abbrev fiberMapLeft (F : X ⟶ Y) {y : Y.total} {P Q : targetFiber F y} (φ : P ⟶ Q) :
    fiberLeft F P ⟶ fiberLeft F Q :=
  (fiberMap F φ).hom.left

/-- The right component of a morphism in a target fiber. -/
abbrev fiberMapRight (F : X ⟶ Y) {y : Y.total} {P Q : targetFiber F y} (φ : P ⟶ Q) :
    fiberRight F P ⟶ fiberRight F Q :=
  (fiberMap F φ).hom.right

/-- The components of a target-fiber morphism form the canonical commuting comparison square. -/
theorem fiberMap_comm (F : X ⟶ Y) {y : Y.total} {P Q : targetFiber F y}
    (φ : P ⟶ Q) :
    fiberMapLeft F φ ≫ fiberComparison F Q =
      fiberComparison F P ≫ (toFunctor F).map (fiberMapRight F φ) := sorry

/-- On morphisms, the fiberwise source endpoint functor selects the right component of the comma
square. -/
@[simp]
theorem fiberSource_map (F : X ⟶ Y) {y : Y.total} {P Q : targetFiber F y}
    (φ : P ⟶ Q) :
    (fiberSource F y).map φ = fiberMapRight F φ := sorry

/-- Pull a presheaf on `X.total` back to the target-based factorization category along its source
endpoint. -/
def sourcePullback {D : Type uD} [Category.{vD} D] (F : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ D) :
    (overTarget F).totalᵒᵖ ⥤ D :=
  (source F).op ⋙ P

/-- Restrict a presheaf on `X.total` to the comparison-index fiber over `y`. -/
def fiberSourcePullback {D : Type uD} [Category.{vD} D] (F : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ D) (y : Y.total) :
    (targetFiber F y)ᵒᵖ ⥤ D :=
  (fiberSource F y).op ⋙ P

end

end CategoryTheory.FiberedCategoryOver.AdjointFactorization
