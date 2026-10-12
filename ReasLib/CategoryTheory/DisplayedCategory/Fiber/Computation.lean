/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber

/-!
# Computation and fullness API for intrinsic displayed fibers

`DisplayedCategory.Fiber` owns the intrinsic category and its inclusion.  This leaf adds the
inverse-to-inclusion operations that downstream code normally expects from a fiber category,
without making the comparison with Mathlib's subtype fiber part of the basic definition.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory.Fiber

variable {D : DisplayedCategory C} {X : C}

/-- Recover an intrinsic-fiber morphism from a total morphism lying over `𝟙 X`. -/
noncomputable def ofLift {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    [(DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) φ] : x ⟶ y :=
  DisplayedCategory.Hom.cast D
    (by
      exact
        (DisplayedCategory.Total.isHomLift_iff (D := D) (𝟙 X) φ).mp
          (inferInstance : (DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) φ) |>.symm)
    φ.displayed

/-- Recover an intrinsic-fiber morphism from a total morphism together with an explicit equality
of its base arrow with the fiber identity.  This equality-driven form is convenient for maps
obtained by dependent reindexing, where installing an `IsHomLift` instance would only duplicate
the stored base equality. -/
noncomputable def ofBase {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    (h : φ.base = 𝟙 X) : x ⟶ y :=
  DisplayedCategory.Hom.cast D h φ.displayed

/-- Standard fiber-style constructor for an intrinsic-fiber morphism. -/
noncomputable def homMk {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    [(DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) φ] : x ⟶ y :=
  ofLift φ

/-- Fiber-style constructor using an explicit base-arrow equality rather than a typeclass
certificate. -/
noncomputable def homMkOfEq {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    (h : φ.base = 𝟙 X) : x ⟶ y :=
  ofBase φ h

/-- Lifting and then recovering a fiber morphism is the identity. -/
@[simp]
theorem ofLift_lift {x y : Fiber D X} (f : x ⟶ y) :
    ofLift (lift f) = f := sorry

/-- The explicit-equality constructor recovers a lifted fiber morphism. -/
@[simp]
theorem ofBase_lift {x y : Fiber D X} (f : x ⟶ y) :
    ofBase (lift f) (by simp) = f := sorry

/-- Recovering and then lifting a total morphism over the fiber identity is the identity. -/
@[simp]
theorem lift_ofLift {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    [(DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) φ] :
    lift (ofLift φ) = φ := sorry

/-- Lifting the explicit-equality reconstruction recovers the original total morphism. -/
@[simp]
theorem lift_ofBase {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    (h : φ.base = 𝟙 X) :
    lift (ofBase φ h) = φ := sorry

/-- The intrinsic-fiber inclusion is faithful. -/
instance inclusion_faithful (D : DisplayedCategory C) (X : C) :
    (inclusion D X).Faithful where
  map_injective := fun {_ _} _ _ h => hom_ext h

@[simp]
theorem homMk_apply {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    [(DisplayedCategory.Total.forget D).IsHomLift (𝟙 X) φ] :
    (inclusion D X).map (homMk φ) = φ := by
  exact lift_ofLift φ

/-- The explicit-equality constructor is sent back to its total morphism by the inclusion. -/
@[simp]
theorem homMkOfEq_apply {x y : Fiber D X}
    (φ : (⟨X, x⟩ : DisplayedCategory.Total D) ⟶ ⟨X, y⟩)
    (h : φ.base = 𝟙 X) :
    (inclusion D X).map (homMkOfEq φ h) = φ := by
  exact lift_ofBase φ h

end DisplayedCategory.Fiber

end CategoryTheory
