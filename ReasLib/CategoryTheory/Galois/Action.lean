module

public import Mathlib.CategoryTheory.Galois.Action

@[expose] public section

universe u v w

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})

/-- A finite-valued functor induces a functor to finite sets equipped with the
canonical action of its automorphism group. -/
def finiteActionFunctor : C ⥤ Action FintypeCat.{w} (Aut F) where
  obj X := Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map morphism := {
    hom := F.map morphism
    comm := fun automorphism ↦ (automorphism.hom.naturality morphism).symm
  }

/-- Forgetting the automorphism action on a finite-valued functor recovers the
original functor. -/
theorem finiteActionFunctor_comp_forget₂_eq :
    finiteActionFunctor F ⋙ forget₂ _ FintypeCat = F := sorry

end CategoryTheory.PreGaloisCategory
