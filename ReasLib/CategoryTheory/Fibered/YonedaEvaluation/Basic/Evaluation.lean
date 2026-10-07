module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.CartesianHom
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-owner fibered Yoneda evaluation

This leaf transports neutral cartesian Yoneda evaluation to the hom-category of fixed
`FiberedCategoryOver` owners. It requires neither a cleavage nor chosen inverse data.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice

variable (X : FiberedCategoryOver C)

/-- Evaluation at the identity object `𝟙 U : U ⟶ U` on morphisms of fibred categories
`C/U ⟶ X`, valued in the canonical fibre `X_U`. -/
@[stacks 0GWI "fibered Yoneda evaluation"]
noncomputable def evaluation (U : C) :
    (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) ⥤ X.p.Fiber U :=
  FiberedCategoryOver.CartesianHom.fromHom
      (FiberedCategoryOver.ofFunctor (Over.forget U)) X ⋙
    CartesianBasedFunctor.Yoneda.evaluation X.p U

namespace evaluation

/-- After forgetting the fibre packaging, evaluation sends a fibred functor to its value at the
identity slice object. -/
@[simp]
theorem obj (U : C) (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (Fiber.fiberInclusion : X.p.Fiber U ⥤ X.total).obj ((evaluation X U).obj F) =
      (FiberedCategoryOver.toFunctor F).obj (Over.mk (𝟙 U)) := sorry

/-- After forgetting the fibre packaging, evaluation sends a `2`-morphism to its component at
the identity slice object. -/
@[simp]
theorem map (U : C) {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (eta : F ⟶ G) :
    (Fiber.fiberInclusion : X.p.Fiber U ⥤ X.total).map ((evaluation X U).map eta) =
      eta.hom.toNatTrans.app (Over.mk (𝟙 U)) := sorry

/-- Evaluating a morphism of fibred categories on the identity object through its fiber functor
agrees with fixed-owner Yoneda evaluation. -/
theorem fiberObj (U : C) (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (fiberFunctor F U).obj (BasedCategory.Yoneda.Identity.fiberObj U) =
      (evaluation X U).obj F := sorry

end evaluation

end FiberedCategoryOver.YonedaSlice

end CategoryTheory

/- Data audit: evaluation is the composite of the fixed-owner forgetful functor and neutral
cartesian Yoneda evaluation; deferred axioms occur only in computation statements. -/
