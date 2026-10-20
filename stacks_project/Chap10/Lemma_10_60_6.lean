module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension
import StacksCheckRecall

/-!
# Lemma 10.60.6

@stack 00KI

The source orders Krull dimension before Hilbert--Samuel degree, so the canonical comparison is
recalled in its symmetric orientation.
-/

@[expose] public section

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Lemma 10.60.6: for a Noetherian local ring `R`, the Krull-dimension condition `dim(R) = 0` is
equivalent to the vanishing of the Hilbert-Samuel degree invariant `d(R) = 0`; in the project this
is exactly the degree-zero specialization of the reusable Hilbert--Samuel dimension comparison. -/
@[stacks 00KI]
#check
  ((Ideal.HilbertSamuel.degree_eq_iff_ringKrullDim_eq (R := R) 0).symm :
    ringKrullDim R = 0 ↔ Ideal.HilbertSamuel.degree R R = 0)

end
