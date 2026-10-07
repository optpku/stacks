module

public import ReasLib.RingTheory.LocalRing.AssociatedGraded
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing
open Ideal.AssociatedGraded

/- Exercise 111.28.4: if `(A, 𝔪, k)` is a Noetherian local ring of embedding
dimension 1, i.e. `Module.finrank k (CotangentSpace A) = 1`, then
`n ↦ Module.finrank k (piece (maximalIdeal A) A n)` is either identically 1,
or else equals 1 on an initial segment and 0 thereafter. -/
@[stacks 02EI] #check (IsLocalRing.finrank_associatedGradedPiece_eq_one_or_eventually_zero :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      Module.finrank (ResidueField R) (CotangentSpace R) = 1 →
        (∀ n : ℕ,
          Module.finrank (ResidueField R)
              (Ideal.AssociatedGraded.piece (maximalIdeal R) R n) = 1) ∨
          ∃ N : ℕ,
            (∀ n : ℕ, n < N →
              Module.finrank (ResidueField R)
                  (Ideal.AssociatedGraded.piece (maximalIdeal R) R n) = 1) ∧
            (∀ n : ℕ, N ≤ n →
              Module.finrank (ResidueField R)
                  (Ideal.AssociatedGraded.piece (maximalIdeal R) R n) = 0))
