module

public import ReasLib.CategoryTheory.Pro.Sequential.Diagonal

@[expose] public section

open CategoryTheory Limits Opposite
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]

/- The source-facing flattening API is provided by the shared diagonal owner. -/
#check (CategoryTheory.Pro.SequentialHom.diagonalPro :
  ∀ {C : Type u} [Category.{v} C]
    (M : ℕ → ℕᵒᵖ ⥤ C)
    (_ : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)), Pro C)

#check (CategoryTheory.Pro.SequentialHom.diagonalProHomComparison :
  ∀ {C : Type u} [Category.{v} C]
    (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)),
    ((Pro.inclusion C).obj
      (CategoryTheory.Pro.SequentialHom.diagonalPro M r)).unop ⟶
      CategoryTheory.Pro.SequentialHom.iteratedHomColimit M r)

#check (CategoryTheory.Pro.SequentialHom.diagonalProHomComparison_bijective :
  ∀ {C : Type u} [Category.{v} C]
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (_ : ∀ k n, n ≤ (r k).reindex n) (N : C),
    Function.Bijective
      ((CategoryTheory.Pro.SequentialHom.diagonalProHomComparison M r).app N))

#check (CategoryTheory.Pro.SequentialHom.isoDiagonalPro :
  ∀ {C : Type u} [Category.{v} C]
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (_ : ∀ k n, n ≤ (r k).reindex n) (P : Pro C)
    (comparison : ((Pro.inclusion C).obj P).unop ⟶
      CategoryTheory.Pro.SequentialHom.iteratedHomColimit M r)
    (_ : ∀ N, Function.Bijective (comparison.app N)),
    P ≅ CategoryTheory.Pro.SequentialHom.diagonalPro M r)

end CategoryTheory.Pro.SequentialHom
