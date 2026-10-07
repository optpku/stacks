module

public import ReasLib.RingTheory.Ideal.SymbolicPower.Cofinality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.16.5: in a complete Noetherian local domain, symbolic powers of a
prime ideal with one-dimensional quotient are cofinal with its ordinary powers. -/
@[stacks 0EB5] #check
  (@Ideal.exists_symbolicPower_le_pow :
    {A : Type u} → [CommRing A] → [IsDomain A] → [IsNoetherianRing A] →
      [IsCompleteLocalRing A] → (𝔭 : Ideal A) → [𝔭.IsPrime] →
      (ringKrullDim (A ⧸ 𝔭) = 1) → (n : ℕ) → (1 ≤ n) →
      ∃ m ≥ n, 𝔭.symbolicPower m ≤ 𝔭 ^ n)
