module

public import Mathlib.RingTheory.Regular.RegularSequence

@[expose] public section

universe u

open IsLocalRing

namespace RingTheory.Sequence

/-- A commutative local ring can contain a regular sequence in its maximal ideal
whose first two entries annihilate a common nonzero element modulo the third. -/
theorem exists_isLocalRing_isRegular_quot_last_annihilated :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (x y z : R),
      IsRegular R [x, y, z] ∧
        Ideal.ofList [x, y, z] ≤ maximalIdeal R ∧
        ∃ δ : R ⧸ Ideal.span {z}, δ ≠ 0 ∧ x • δ = 0 ∧ y • δ = 0 := sorry

end RingTheory.Sequence
