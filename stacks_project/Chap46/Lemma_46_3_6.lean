module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Generators
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : CommRingCat.{u}}
variable {F : ModuleValuedFunctor.bundled.{u, u} A}

/- Lemma 46.3.6: every adequate functor on `Alg_A` admits an objectwise surjective
morphism from a direct sum of linearly adequate functors. -/
@[stacks 06UX]
#check (ModuleValuedFunctor.TensorAdequate.exists_surjective_from_coproduct
  (A := A) (F := F) :
    ModuleValuedFunctor.TensorAdequate F →
      ∃ (ι : Type u) (G : ι → ModuleValuedFunctor.bundled.{u, u} A)
        (L : ModuleValuedFunctor.bundled.{u, u} A) (ιG : ∀ i, G i ⟶ L)
        (_ : IsColimit (Cofan.mk L ιG)) (π : L ⟶ F),
        (∀ i, ModuleValuedFunctor.TensorLinearlyAdequate (G i)) ∧
          ∀ B, Function.Surjective (π.app B))
