module

public import ReasLib.RingTheory.MvPolynomial.PhamBrieskorn.Localization
import StacksCheckRecall

universe u

/- Example 89.9.1: Let `k` be a field. The ring
`A = k[x, y, z] ⧸ (x ^ r + y ^ s + z ^ t)` is a UFD for pairwise coprime
exponents `r`, `s`, `t`. -/
@[stacks 0AE9] #check
  (MvPolynomial.PhamBrieskorn.instUniqueFactorizationMonoid :
    ∀ (k : Type u) [Field k] (r s t : ℕ)
      [Fact (Nat.Coprime r s)] [Fact (Nat.Coprime r t)] [Fact (Nat.Coprime s t)],
      UniqueFactorizationMonoid (MvPolynomial.PhamBrieskorn.Ring k r s t))
