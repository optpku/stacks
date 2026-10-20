module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorAdequate

variable {A : CommRingCat.{u}}

/-- Every adequate module-valued functor is the objectwise-surjective image of a
coproduct of linearly adequate module-valued functors. -/
theorem exists_surjective_from_coproduct
    {F : ModuleValuedFunctor.bundled.{u, u} A}
    (hF : ModuleValuedFunctor.TensorAdequate F) :
    ∃ (ι : Type u) (G : ι → ModuleValuedFunctor.bundled.{u, u} A)
      (L : ModuleValuedFunctor.bundled.{u, u} A) (ιG : ∀ i, G i ⟶ L)
      (_ : IsColimit (Cofan.mk L ιG)) (π : L ⟶ F),
      (∀ i, ModuleValuedFunctor.TensorLinearlyAdequate (G i)) ∧
        ∀ B, Function.Surjective (π.app B) := sorry

end ModuleValuedFunctor.TensorAdequate
