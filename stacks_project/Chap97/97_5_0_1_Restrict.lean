module

public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction

/-!
# Restriction of fibre objects along a base morphism

The canonical restriction operations and their compatibility with groupoid-fibred morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open CategoryTheory.FiberedCategoryOver.Groupoids

universe u₁ u₂ v₁ v₂ u v w vS

#check (CategoryTheory.Functor.Fiber.restrictObj_comp :
  ∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
    {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V W : 𝒮} (ξ : p.Fiber U)
    (f : V ⟶ U) (g : W ⟶ V),
    restrictObj (restrictObj ξ f) g ≅ restrictObj ξ (g ≫ f))

#check (CategoryTheory.FiberedCategoryOver.Groupoids.fiberFunctor_restrictObj :
  ∀ {C : Type u} [Category.{v} C] {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (F : X ⟶ Y) {U Z : C} (x : X.p.Fiber U) (f : Z ⟶ U),
    (fiberFunctor F Z).obj (restrictObj x f) ≅
      restrictObj ((fiberFunctor F U).obj x) f)
