module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

/-!
# Yoneda representatives of total objects

Objects of a category fibred in groupoids over schemes determine slice
morphisms, and slice morphisms can be evaluated at the identity object.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids.YonedaSlice
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The 2-Yoneda 1-morphism `x : U ⟶ X` associated to an object `x` of `X`
lying over a scheme `U`. -/
def yonedaHom (X : GroupoidsOver S) (x : X.total) :
    slice (X.p.obj x) ⟶ X :=
  representative ⟨x, rfl⟩

/-- `yonedaHom X x` is the groupoid-fibred Yoneda representative of the fiber
object `⟨x, rfl⟩`. -/
theorem yonedaHom_spec (X : GroupoidsOver S) (x : X.total) :
    yonedaHom X x = representative ⟨x, rfl⟩ := rfl

/-- Evaluate a 1-morphism `f : slice U ⟶ X` at the identity object of `U`. -/
def evalId {X : GroupoidsOver S} {U : Over S} (f : GroupoidsOver.slice U ⟶ X) : X.total :=
  Functor.Fiber.fiberInclusion.obj
    ((FiberedCategoryOver.Groupoids.fiberFunctor f U).obj
      (BasedCategory.Yoneda.Identity.fiberObj U))

/-- `evalId f` is the image of the identity slice object under the fiber functor
of `f`. -/
theorem evalId_eq {X : GroupoidsOver S} {U : Over S} (f : GroupoidsOver.slice U ⟶ X) :
    evalId f =
      Functor.Fiber.fiberInclusion.obj
        ((FiberedCategoryOver.Groupoids.fiberFunctor f U).obj
          (BasedCategory.Yoneda.Identity.fiberObj U)) :=
  rfl

end AlgebraicGeometry.GroupoidsOver

