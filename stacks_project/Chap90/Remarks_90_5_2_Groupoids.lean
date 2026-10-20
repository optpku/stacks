module

public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# The bicategory of categories cofibered in groupoids

The reusable cofibered-groupoid bicategory and its object, morphism, identity, and product API
are owned by `ReasLib.CategoryTheory.Cofibered.InGroupoids`.
-/

@[expose] public section

namespace CategoryTheory

open scoped Bicategory BasedFunctor

universe u v w vS vB
variable {C : Type u} [Category.{v} C] {F : Type w} [Category.{vS} F]
variable (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]

#check (CategoryTheory.CofiberedCategoryOver.Groupoids.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.ofFunctor p :
  CofiberedCategoryOver.Groupoids.{u, v, w, vS} C)
variable {X Y : CofiberedCategoryOver.Groupoids.{u, v, w, vS} C} (φ : X ⟶ Y)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.toBasedFunctor φ :
  X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.product :
  CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C →
    CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C →
      CofiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C)

end CategoryTheory
