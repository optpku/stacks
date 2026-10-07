module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
import StacksCheckRecall

/-!
# Definition 10.59.6

@stack 09CA
-/

@[expose] public section

universe u v

open IsLocalRing
open scoped Ideal

section

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Definition 10.59.6 (Tag 09CA): the eventual Hilbert polynomial is owned by the
   neutral `Ideal.HilbertSamuel` API; this chapter file is the source-facing recall block. -/
@[stacks 09CA]
#check Ideal.HilbertSamuel.phiPolynomial (maximalIdeal R) M

@[stacks 09CA "existence and uniqueness"]
#check @Ideal.HilbertSamuel.existsUnique_phiPolynomial

@[stacks 09CA "eventual polynomial specification"]
#check @Ideal.HilbertSamuel.phiPolynomial_spec

@[stacks 09CA "polynomial equality criterion"]
#check @Ideal.HilbertSamuel.eq_phiPolynomial

@[stacks 09CA "eventual equality criterion"]
#check @Ideal.HilbertSamuel.eventuallyEq_phi_iff_eq_phiPolynomial

end
