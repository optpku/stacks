module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal functors restricted to full subcategories

A strong monoidal functor carrying one monoidal object property into another restricts to a
strong monoidal functor between the corresponding full subcategories. The tensorator data are
the ambient tensorators; only their property-insensitive coherence is lifted.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}
variable [P.IsMonoidal] [Q.IsMonoidal]
variable (F : C ⥤ D) [F.Monoidal]
variable (hF : P ≤ Q.inverseImage F)

/-- The ambient unit isomorphism lifted to the two full monoidal subcategories. -/
@[stacks 001D "unit comparison for a restricted monoidal functor"]
def unitIso :
    𝟙_ Q.FullSubcategory ≅ (restrict F hF).obj (𝟙_ P.FullSubcategory) :=
  Q.isoMk (Functor.Monoidal.εIso F)

/-- The ambient tensorator lifted to the two full monoidal subcategories. -/
@[stacks 001D "tensor comparison for a restricted monoidal functor"]
def tensorIso (X Y : P.FullSubcategory) :
    (restrict F hF).obj X ⊗ (restrict F hF).obj Y ≅
      (restrict F hF).obj (X ⊗ Y) :=
  Q.isoMk (Functor.Monoidal.μIso F X.obj Y.obj)

/-- Naturality of the restricted tensorator in its left variable. -/
theorem tensorIso_natural_left {X Y : P.FullSubcategory} (f : X ⟶ Y)
    (Z : P.FullSubcategory) :
    (restrict F hF).map f ▷ (restrict F hF).obj Z ≫
        (tensorIso F hF Y Z).hom =
      (tensorIso F hF X Z).hom ≫ (restrict F hF).map (f ▷ Z) := sorry

/-- Naturality of the restricted tensorator in its right variable. -/
theorem tensorIso_natural_right (X : P.FullSubcategory)
    {Y Z : P.FullSubcategory} (f : Y ⟶ Z) :
    (restrict F hF).obj X ◁ (restrict F hF).map f ≫
        (tensorIso F hF X Z).hom =
      (tensorIso F hF X Y).hom ≫ (restrict F hF).map (X ◁ f) := sorry

/-- The restricted tensorator respects the associators of the full subcategories. -/
theorem tensorIso_associativity (X Y Z : P.FullSubcategory) :
    (tensorIso F hF X Y).hom ▷ (restrict F hF).obj Z ≫
        (tensorIso F hF (X ⊗ Y) Z).hom ≫
          (restrict F hF).map (α_ X Y Z).hom =
      (α_ ((restrict F hF).obj X) ((restrict F hF).obj Y)
        ((restrict F hF).obj Z)).hom ≫
        (restrict F hF).obj X ◁ (tensorIso F hF Y Z).hom ≫
        (tensorIso F hF X (Y ⊗ Z)).hom := sorry

/-- The restricted unit and tensor isomorphisms respect the left unitor. -/
theorem tensorIso_left_unitality (X : P.FullSubcategory) :
    (λ_ ((restrict F hF).obj X)).hom =
      (unitIso F hF).hom ▷ (restrict F hF).obj X ≫
        (tensorIso F hF (𝟙_ P.FullSubcategory) X).hom ≫
          (restrict F hF).map (λ_ X).hom := sorry

/-- The restricted unit and tensor isomorphisms respect the right unitor. -/
theorem tensorIso_right_unitality (X : P.FullSubcategory) :
    (ρ_ ((restrict F hF).obj X)).hom =
      (restrict F hF).obj X ◁ (unitIso F hF).hom ≫
        (tensorIso F hF X (𝟙_ P.FullSubcategory)).hom ≫
          (restrict F hF).map (ρ_ X).hom := sorry

/-- The strong monoidal core of a functor restricted to full monoidal subcategories. -/
@[stacks 001D "restricted monoidal functor core"]
def coreMonoidal : (restrict F hF).CoreMonoidal where
  εIso := unitIso F hF
  μIso := tensorIso F hF
  μIso_hom_natural_left := tensorIso_natural_left F hF
  μIso_hom_natural_right := fun X f ↦ tensorIso_natural_right F hF X f
  associativity := tensorIso_associativity F hF
  left_unitality := tensorIso_left_unitality F hF
  right_unitality := tensorIso_right_unitality F hF

/-- Restriction preserves the canonical strong monoidal structure. -/
@[stacks 001D "restriction of a monoidal functor", implicit_reducible]
instance (priority := 100) monoidal : (restrict F hF).Monoidal :=
  (coreMonoidal F hF).toMonoidal

/-- Forgetting the restricted unit isomorphism recovers the ambient unit isomorphism. -/
@[simp]
theorem unitIso_hom :
    (unitIso F hF).hom.hom = (Functor.Monoidal.εIso F).hom := sorry

/-- Forgetting the inverse restricted unit isomorphism recovers the ambient inverse. -/
@[simp]
theorem unitIso_inv :
    (unitIso F hF).inv.hom = (Functor.Monoidal.εIso F).inv := sorry

/-- Forgetting the restricted tensorator recovers the ambient tensorator. -/
@[simp]
theorem tensorIso_hom (X Y : P.FullSubcategory) :
    (tensorIso F hF X Y).hom.hom =
      (Functor.Monoidal.μIso F X.obj Y.obj).hom := sorry

/-- Forgetting the inverse restricted tensorator recovers the ambient inverse tensorator. -/
@[simp]
theorem tensorIso_inv (X Y : P.FullSubcategory) :
    (tensorIso F hF X Y).inv.hom =
      (Functor.Monoidal.μIso F X.obj Y.obj).inv := sorry

/-- The underlying lax unit map of the restricted functor is the ambient lax unit map. -/
@[simp]
theorem ε_hom :
    (Functor.LaxMonoidal.ε (restrict F hF)).hom =
      Functor.LaxMonoidal.ε F := sorry

/-- The underlying lax tensor map of the restricted functor is the ambient lax tensor map. -/
@[simp]
theorem μ_hom (X Y : P.FullSubcategory) :
    (Functor.LaxMonoidal.μ (restrict F hF) X Y).hom =
      Functor.LaxMonoidal.μ F X.obj Y.obj := sorry

/-- The underlying oplax unit map of the restricted functor is the ambient oplax unit map. -/
@[simp]
theorem η_hom :
    (Functor.OplaxMonoidal.η (restrict F hF)).hom =
      Functor.OplaxMonoidal.η F := sorry

/-- The underlying oplax tensor map of the restricted functor is the ambient oplax tensor map. -/
@[simp]
theorem δ_hom (X Y : P.FullSubcategory) :
    (Functor.OplaxMonoidal.δ (restrict F hF) X Y).hom =
      Functor.OplaxMonoidal.δ F X.obj Y.obj := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
