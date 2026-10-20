module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassCopresheaf
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Elements

/-!
# The canonical based morphism to fibrewise isomorphism classes

The canonical functor from a category cofibered in groupoids to the category of elements of its
covariant fibrewise isomorphism-class functor.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v uF vF

namespace CategoryTheory.BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

/-- The quotient-class computation for the canonical functor on a total-category morphism. -/
theorem toIsoClassFunctor_map_property (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {x y : F} (φ : x ⟶ y) :
    (Functor.fiberIsoClassCopresheaf p).map (p.map φ)
        (Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))) =
      Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj y = p.obj y)) := sorry

/-- The underlying functor of the canonical morphism to fibrewise isomorphism classes. -/
noncomputable def toIsoClassFunctor (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    F ⥤ (Functor.fiberIsoClassCopresheaf p).Elements where
  obj x := ⟨p.obj x,
    Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩
  map {x y} φ := ⟨p.map φ, toIsoClassFunctor_map_property p φ⟩
  map_id := by
    intro X
    apply CategoryOfElements.ext
    simp
  map_comp := by
    intro X Y Z f g
    apply CategoryOfElements.ext
    simp

/-- The underlying canonical functor commutes strictly with the projection to the base. -/
theorem toIsoClassFunctor_comp_π (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    toIsoClassFunctor p ⋙ CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p) = p := rfl

/-- The canonical based morphism to the category of fibrewise isomorphism classes. -/
noncomputable def toIsoClass (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p)) :=
  BasedFunctor.ofFunctor (toIsoClassFunctor p) (toIsoClassFunctor_comp_π p)

/-- On objects, the canonical underlying functor returns the base object and fibre class. -/
theorem toIsoClassFunctor_obj (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] (x : F) :
    (toIsoClassFunctor p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩ := rfl

/-- On objects, the canonical based morphism returns the base object and fibre class. -/
theorem toIsoClass_obj (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] (x : F) :
    (toIsoClass p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩ := rfl

/-- The canonical based morphism maps a total-category arrow to its base arrow. -/
theorem toIsoClass_map (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {x y : F} (φ : x ⟶ y) :
    (CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p)).map ((toIsoClass p).map φ) =
      p.map φ := rfl

/-- The canonical based morphism commutes strictly with the projection to the base. -/
theorem toIsoClass_comp_π (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    (toIsoClass p).toFunctor ⋙
        CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p) = p := rfl

/-- The canonical based morphism has a lift along every arrow of the base. -/
theorem toIsoClass_exists_lift (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) {y : (Functor.fiberIsoClassCopresheaf p).Elements}
    {x : F} (α : y ⟶ (toIsoClass p).obj x)
    (hα : (CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p)).IsHomLift f α) :
    ∃ (x' : F) (β : x' ⟶ x) (γ : (toIsoClass p).obj x' ⟶ y),
      p.IsHomLift f β ∧
        (CategoryOfElements.π (Functor.fiberIsoClassCopresheaf p)).IsHomLift (𝟙 U) γ ∧
          γ ≫ α = (toIsoClass p).map β := sorry

end CategoryTheory.BasedFunctor
