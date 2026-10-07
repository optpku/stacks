module

public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

noncomputable section

/- Theorem 19.11.7: every Grothendieck abelian category admits functorial injective embeddings. -/
@[stacks 079H] #check
  fun (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] ↦
    (inferInstance : HasFunctorialInjectives C)

end

end CategoryTheory
