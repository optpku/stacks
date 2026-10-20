module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Nagata

@[expose] public section

/-!
# Descent of p-th roots from adic completions

@stack 09E2

This module records the p-th-root descent consequence of analytic
unramifiedness for local Nagata domains.
-/

universe u

open IsLocalRing

namespace NagataRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [NagataRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]

/-- Lemma 10.162.18, tag `09E2`: if an element of a local Nagata domain has a
`p`-th root in its maximal-ideal completion, then it already has one in the
domain. -/
@[stacks 09E2]
theorem exists_pth_root_of_completion {a : A}
    (hroot : ∃ alpha : AdicCompletion (maximalIdeal A) A,
      alpha ^ p = algebraMap A (AdicCompletion (maximalIdeal A) A) a) :
    ∃ b : A, b ^ p = a := sorry

end NagataRing
