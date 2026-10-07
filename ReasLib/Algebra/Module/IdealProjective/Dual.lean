module

public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Dual

@[expose] public section

/-!
# Duals and projective-factor ideals

@stack 0G96

For a finite module, dualization carries each projective factorisation of a scalar endomorphism
to one on the dual.  The natural statement is an inclusion of projective-factor ideals.
-/

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M] [Module.Finite R M]

namespace projectiveFactorIdeal

/-- The projective-factor ideal of a finite module is contained in that of its dual. -/
@[stacks 0G96 "projective-factor ideal under duality"]
theorem le_dual :
    projectiveFactorIdeal R M ≤ projectiveFactorIdeal R (Dual R M) := sorry

end projectiveFactorIdeal

namespace IsIdealProjective

/-- Lemma 15.71.7: the dual of a finite ideal-projective module is ideal-projective. -/
@[stacks 0G96 "duality for ideal-projective modules"]
theorem dual {I : Ideal R} (h : IsIdealProjective I M) :
    IsIdealProjective I (Dual R M) := sorry

end IsIdealProjective

end Module
