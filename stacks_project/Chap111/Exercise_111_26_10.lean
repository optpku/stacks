module

public import ReasLib.RingTheory.MvPolynomial.FermatHypersurface
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory MvPolynomial.FermatHypersurface

/- Exercise 111.26.10 (1): the Hilbert function of the standard-graded Fermat hypersurface
ring `B = k[x, y, z] ⧸ (x ^ d + y ^ d + z ^ d)`, with `deg x = deg y = deg z = 1` and
`φ(M) = dim_k(M)`, equals the closed-form sequence `hilbertFunction d` whenever the Fermat
equation is nonzero. -/
@[stacks 02E8] #check (MvPolynomial.FermatHypersurface.hilbertFunction_eq :
  ∀ (k : Type u) [Field k] (d : ℕ), equation k d ≠ 0 → ∀ (n : ℤ),
    GradedModule.hilbertFunction (ModuleCat.K0.finiteLength k) (intGrading k d) n =
      hilbertFunction d n)

/- Exercise 111.26.10 (1), zero-equation case: the Hilbert function is the ternary
multichoose dimension in nonnegative degrees and zero in negative degrees. Together
with the nonzero-equation case above, this exhausts all fields and natural exponents,
including exponent zero. -/
@[stacks 02E8] #check (MvPolynomial.FermatHypersurface.hilbertFunction_eq_of_equation_eq_zero :
  ∀ (k : Type u) [Field k] (d : ℕ), equation k d = 0 → ∀ (n : ℤ),
    GradedModule.hilbertFunction (ModuleCat.K0.finiteLength k) (intGrading k d) n =
      if 0 ≤ n then (Nat.multichoose 3 n.toNat : ℤ) else 0)

/- Exercise 111.26.10 (2): the standard-graded Fermat hypersurface ring has a Hilbert
polynomial with respect to `φ(M) = dim_k(M)`. -/
@[stacks 02E8] #check (MvPolynomial.FermatHypersurface.hasHilbertPolynomial :
  ∀ (k : Type u) [Field k] (d : ℕ),
    GradedModule.HasHilbertPolynomial (ModuleCat.K0.finiteLength k) (intGrading k d))
