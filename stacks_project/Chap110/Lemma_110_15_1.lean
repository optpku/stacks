module

public import ReasLib.RingTheory.Sequence.Regularity.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

namespace RingTheory.Sequence

/- Lemma 110.15.1: there exists a local ring `R` and a regular sequence `x`, `y`, `z`
in the maximal ideal such that some nonzero `δ` in `R ⧸ Ideal.span {z}` is annihilated
by both `x` and `y`. -/
@[stacks 0640] #check (RingTheory.Sequence.exists_isLocalRing_isRegular_quot_last_annihilated :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (x y z : R),
      IsRegular R [x, y, z] ∧
        Ideal.ofList [x, y, z] ≤ maximalIdeal R ∧
        ∃ δ : R ⧸ Ideal.span {z}, δ ≠ 0 ∧ x • δ = 0 ∧ y • δ = 0)

end RingTheory.Sequence
