module

import ReasLib.RingTheory.RingHom.Fiber.FiniteType
import StacksCheckRecall

universe u v

/- Lemma 37.31.2: for a finite-type ring map `φ : R →+* S`, if the fibers of
the polynomial evaluation map sending `X` to `a` have Krull dimension at most
`d`, then the same bound holds after sending `X` to `a ^ n + b` for every
sufficiently large `n`. -/
@[stacks 0GTF] #check
  (RingHom.FibersKrullDimLE.eventually_eval₂_pow_add :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S]
      (φ : R →+* S) (h_finiteType : φ.FiniteType) (d : ℕ) (a b : S),
      RingHom.FibersKrullDimLE d (Polynomial.eval₂RingHom φ a) →
        ∃ n₀ : ℕ, ∀ n ≥ n₀,
          RingHom.FibersKrullDimLE d (Polynomial.eval₂RingHom φ (a ^ n + b)))
