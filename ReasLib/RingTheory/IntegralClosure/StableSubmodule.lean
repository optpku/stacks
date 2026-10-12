/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integrality from a stable finite submodule

@stack 052I

The finite stable-submodule criterion is a reusable algebraic owner.  The source-facing existential
form is kept beside the canonical fixed-submodule form so callers do not unpack the same witness
manually.
-/

universe u v

namespace Submodule

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.36.2, canonical form: a finite `R`-submodule of `S` containing `1` and stable under
multiplication by `y` makes `y` integral over `R`. -/
@[stacks 052I "finite stable-submodule criterion"]
theorem isIntegral_of_fg_stable {y : S} {M : Submodule R S}
    (hfg : M.FG) (h1 : (1 : S) ∈ M) (hstable : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := sorry

/-- Lemma 10.36.2, source-facing form: the same conclusion from an existential stable submodule.
-/
@[stacks 052I "source existential form"]
theorem isIntegral_of_exists_fg_stable {y : S}
    (hM : ∃ M : Submodule R S, M.FG ∧ (1 : S) ∈ M ∧ ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := sorry

end Submodule
