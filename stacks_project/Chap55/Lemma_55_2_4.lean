module

public import ReasLib.LinearAlgebra.BilinearForm.IntegralLattice
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 55.2.4 (1): the map from L / (A ⊕ B) to A# / A is injective. -/
@[stacks 0C6V] #check (IntegralLatticePair.leftMap_injective :
  ∀ {V : Type u} [AddCommGroup V] [Module ℚ V] (C : IntegralLatticePair V),
    Function.Injective C.leftMap)

/- Lemma 55.2.4 (2): the map from L / (A ⊕ B) to B# / B is injective. -/
@[stacks 0C6V] #check (IntegralLatticePair.rightMap_injective :
  ∀ {V : Type u} [AddCommGroup V] [Module ℚ V] (C : IntegralLatticePair V),
    Function.Injective C.rightMap)

/- Lemma 55.2.4 (3): the left cokernel is a quotient of L# / L. -/
@[stacks 0C6V] #check (IntegralLatticePair.leftCokernelMap_surjective :
  ∀ {V : Type u} [AddCommGroup V] [Module ℚ V] (C : IntegralLatticePair V),
    Function.Surjective C.leftCokernelMap)

/- Lemma 55.2.4 (4): the right cokernel is a quotient of L# / L. -/
@[stacks 0C6V] #check (IntegralLatticePair.rightCokernelMap_surjective :
  ∀ {V : Type u} [AddCommGroup V] [Module ℚ V] (C : IntegralLatticePair V),
    Function.Surjective C.rightCokernelMap)
