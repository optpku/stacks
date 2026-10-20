module

public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Extended

/-! Compatibility check for the extended relative Čech complex. -/

open CategoryTheory Functor FiberedCategoryOver.Groupoids FiberedCategoryOver.Groupoids.Cech
open scoped Bicategory Simplicial

universe u v w vS wA

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.extended :
  ∀ (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G],
    CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ)
