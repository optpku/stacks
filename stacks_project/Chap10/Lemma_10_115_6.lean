/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Prime
import StacksCheckRecall

@[expose] public section

/-!
# Prime-Ideal Noether Normalization

@stack 051P
-/

noncomputable section

open MvPolynomial
open MvPolynomial.NoetherNormalization

universe u

section

variable {k : Type u} [Field k]
variable {n : ℕ}
variable (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime]

/- Lemma 10.115.6: if `q` is a prime ideal of `k[x_1, ..., x_n]` and
`r = Cardinal.toNat (Algebra.trdeg k q.ResidueField)`, a finite polynomial self-map
contracts `q` to the tail coordinate ideal `(y_{r + 1}, ..., y_n)`. -/
@[stacks 051P]
#check (exists_finite_comap_eq_tailIdeal q :
  ∃ φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
    φ.Finite ∧
      Ideal.comap φ q =
        tailIdeal k n (Cardinal.toNat (Algebra.trdeg k q.ResidueField)))

/- The reusable owner exposes the coordinate ideal and its elementary API. -/
#check @MvPolynomial.NoetherNormalization.tailIdeal
#check @MvPolynomial.NoetherNormalization.tailIdeal_def
#check @MvPolynomial.NoetherNormalization.X_mem_tailIdeal
#check @MvPolynomial.NoetherNormalization.tailIdeal_mono
#check @MvPolynomial.NoetherNormalization.tailIdeal_eq_bot_of_le
#check @MvPolynomial.NoetherNormalization.exists_finite_comap_eq_tailIdeal

end
