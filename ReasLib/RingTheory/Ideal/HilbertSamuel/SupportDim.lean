module

public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Degree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel degree and module support dimension

@stack 00KQ
@stack 00L8

This file owns the reusable bridges from the Hilbert--Samuel degree to the
dimension of a module and from an ambient ring to a quotient ring.  The
source-facing chapter statements are specializations of these interfaces;
the shared statements deliberately expose the canonical `degree` and
`Module.supportDim` owners.
-/

@[expose] public section

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 10.62.6 (00L8): the Hilbert--Samuel degree of a finite module,
transported to `WithBot ℕ∞`, is its support dimension. -/
@[stacks 00L8 "Hilbert-Samuel degree equals module support dimension"]
theorem map_degree_eq_supportDim :
    Nat.castOrderEmbedding.withBotMap (degree R M) = Module.supportDim R M := sorry

/-- Proposition 10.60.9 (00KQ) bridge: viewing a quotient ring as a module over
the ambient local ring does not change its Hilbert--Samuel degree.  The quotient
is required to carry its local Noetherian structure explicitly; this keeps the
bridge independent of any chapter-specific construction of those instances. -/
@[stacks 00KQ "quotient-ring Hilbert-Samuel degree"]
theorem degree_quotient_self {J : Ideal R}
    [IsLocalRing (R ⧸ J)] [IsNoetherianRing (R ⧸ J)] :
    degree R (R ⧸ J) = degree (R ⧸ J) (R ⧸ J) := sorry

end Ideal.HilbertSamuel
