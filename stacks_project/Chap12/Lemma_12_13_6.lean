module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import StacksCheckRecall

@[expose] public section

open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/-
Lemma 12.13.6: a short exact sequence of chain complexes in an abelian category yields the
canonical exact homology segment
`H_i(A_•) ⟶ H_i(B_•) ⟶ H_i(C_•) ⟶ H_{i-1}(A_•) ⟶ H_{i-1}(B_•) ⟶ H_{i-1}(C_•)`,
with connecting morphism
`hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))`. This is exactly the owner theorem
`HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the chain-complex
shape `ComplexShape.down ℤ`. -/
@[stacks 0111]
#check (composableArrows₅_exact hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) :
    (composableArrows₅ hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))).Exact)

end CategoryTheory
