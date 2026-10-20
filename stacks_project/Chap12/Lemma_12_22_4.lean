module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import StacksCheckRecall

@[expose] public section

open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1}))}
  (hS : S.ShortExact)

/- Lemma 12.22.4 [011Y]: a short exact sequence of differential objects yields the canonical
periodic exact five-arrow homology segment. -/
@[stacks 011Y]
#check (composableArrows₅_exact hS PUnit.unit PUnit.unit rfl :
  (composableArrows₅ hS PUnit.unit PUnit.unit rfl).Exact)

end CategoryTheory
