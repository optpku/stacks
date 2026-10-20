module

public import stacks_project.Chap56.Lemma_56_3_8
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped ModuleCat.Algebra

universe u

/- Lemma 56.3.9 -/
@[stacks 0GP1] #check (ModuleCat.equivalence_tensor_invertible_linear :
    ∀ {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [CommRing B] [Algebra R B]
      (F : ModuleCat A ⥤ ModuleCat B) [F.IsEquivalence] [F.Linear R],
      ∃ (e : A ≃ₐ[R] B) (L : ModuleCat B),
        Module.Invertible B L ∧
        Nonempty (F ≅
          ModuleCat.extendScalars e.toRingHom ⋙
            tensorRight L))
