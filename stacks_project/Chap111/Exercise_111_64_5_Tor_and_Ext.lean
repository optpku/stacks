module

public import ReasLib.RingTheory.LocalRing.Tor
public import ReasLib.RingTheory.LocalRing.Ext
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing CategoryTheory CategoryTheory.Abelian

/- Positive exponents are necessary: at `n = 0`, `A ⧸ maximalIdeal A ^ n` is zero,
whereas `Ideal.AssociatedGraded.piece (maximalIdeal A) A 0` is the residue field. -/

/- Exercise 111.64.5 (Tor and Ext) (1): the first Tor module has residue-field dimension
`φ(n)`, the dimension of the degree-`n` associated graded piece, for `1 ≤ n`. -/
@[stacks 0GRX] #check (IsLocalRing.finrank_tor_one_quotient_pow_residueField :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {n : ℕ}, 1 ≤ n →
    Module.finrank (ResidueField A) (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) =
      Module.finrank (ResidueField A)
        (Ideal.AssociatedGraded.piece (maximalIdeal A) A n))

/- Exercise 111.64.5 (Tor and Ext) (2): the first Ext group has residue-field dimension
`φ(n)`, the dimension of the degree-`n` associated graded piece, for `1 ≤ n`. -/
@[stacks 0GRX] #check (IsLocalRing.finrank_ext_one_quotient_pow_residueField :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {n : ℕ}, 1 ≤ n →
    Module.finrank (ResidueField A)
        (Ext (ModuleCat.of A (A ⧸ maximalIdeal A ^ n)) (ModuleCat.of A (ResidueField A)) 1) =
      Module.finrank (ResidueField A)
        (Ideal.AssociatedGraded.piece (maximalIdeal A) A n))
