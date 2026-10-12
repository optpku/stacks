/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.MvPolynomial
import StacksCheckRecall

/-!
# Countably generated polynomial rings are N-2 and non-Noetherian

The two N-2 statements are owned by the countable multivariate-polynomial leaf.  The two
non-Noetherian statements are direct specializations of the generic infinite-variable criterion.

@stack 0350
-/

@[expose] public section

universe u

section

variable (k : Type u) [Field k]

@[stacks 0350 "(1), N-2 over a field"]
#check MvPolynomial.isN2Ring_pnat_of_field k

@[stacks 0350 "(2), non-Noetherian over a field"]
#check (MvPolynomial.not_isNoetherianRing_of_infinite (R := k) (σ := ℕ+) :
  ¬ IsNoetherianRing (MvPolynomial ℕ+ k))

end


@[stacks 0350 "(3), N-2 over the integers"]
#check MvPolynomial.isN2Ring_pnat_int

@[stacks 0350 "(4), non-Noetherian over the integers"]
#check (MvPolynomial.not_isNoetherianRing_of_infinite (R := ℤ) (σ := ℕ+) :
  ¬ IsNoetherianRing (MvPolynomial ℕ+ ℤ))
