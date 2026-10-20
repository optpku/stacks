module

public import ReasLib.CategoryTheory.Fibered.AutomorphismFunctor

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

/- The selected-cleavage automorphism functor on the under-category of the image
of a total-category object. -/
#check (CategoryTheory.Functor.autFunctor :
  {C : Type u₁} → [Category.{v₁} C] → {F : Type u₂} → [Category.{v₂} F] →
    (p : F ⥤ C) → [Functor.IsFibered.InGroupoids p.op] → (x : F) →
      Under (p.obj x) ⥤ Type v₂)
