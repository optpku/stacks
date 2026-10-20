module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import StacksCheckRecall

@[expose] public section

open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/- Lemma 12.13.12: a short exact sequence of cochain complexes in an abelian category yields the
canonical exact cohomology segment
`H^i(A^•) ⟶ H^i(B^•) ⟶ H^i(C^•) ⟶ H^(i + 1)(A^•) ⟶ H^(i + 1)(B^•) ⟶ H^(i + 1)(C^•)`,
with connecting morphism `hS.δ i (i + 1) (up_mk i (i + 1) rfl)`. This is exactly the owner
theorem `HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the
cochain shape `ComplexShape.up ℤ`. -/
@[stacks 0117]
#check (HomologicalComplex.HomologySequence.composableArrows₅_exact hS i (i + 1)
  (up_mk i (i + 1) rfl) :
    (composableArrows₅ hS i (i + 1) (up_mk i (i + 1) rfl)).Exact)

/- Functoriality companion: a morphism of short exact sequences of cochain complexes induces a
morphism between the corresponding exact cohomology segments in degree `i`. This is the
`ComplexShape.up ℤ` specialization of the owner map `mapComposableArrows₅`. -/
variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
variable (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

#check (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1)
  (up_mk i (i + 1) rfl) :
    composableArrows₅ hS₁ i (i + 1) (up_mk i (i + 1) rfl) ⟶
      composableArrows₅ hS₂ i (i + 1) (up_mk i (i + 1) rfl))

/- Shift-compatibility companion: the cohomology functor on cochain complexes carries the
canonical shift isomorphisms `H^i(K⟦n⟧) ≅ H^(i + n)(K)` used to identify the long exact sequence
of a shifted short exact sequence with the shifted long exact sequence. This is the source-facing
cochain owner `CochainComplex.ShiftSequence.shiftIso`. -/
#check CochainComplex.ShiftSequence.shiftIso

end CategoryTheory
