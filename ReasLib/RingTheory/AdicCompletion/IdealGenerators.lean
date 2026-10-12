/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
@stack 090S
@stack 090T
# Finite-generator adic completeness interfaces

This leaf owns the finite-generator reductions for adic precompleteness,
completion surjectivity, and completeness monotonicity. The APIs are phrased
in Mathlib's canonical adic-completion predicates; chapter names remain
source-facing bridges.
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace IsPrecomplete

/-- Lemma 10.96.7 (Stacks 090S): precompleteness for each principal generator
implies precompleteness for the ideal spanned by a finite generating set. -/
@[stacks 090S "finite-generator reduction for adic precompleteness"]
theorem of_span_eq_of_generatorwise
    {I : Ideal R} (s : Finset R) (hI : Ideal.span (s : Set R) = I)
    (hpre : ∀ f ∈ s, IsPrecomplete (Ideal.span ({f} : Set R)) M) :
    IsPrecomplete I M := sorry

end IsPrecomplete

namespace AdicCompletion

/-- Lemma 10.96.7 (Stacks 090S): surjectivity of the completion map for every
principal generator implies surjectivity for the finitely generated ideal. -/
@[stacks 090S "finite-generator reduction for completion surjectivity"]
theorem surjective_of_span_eq_of_generatorwise
    {I : Ideal R} (s : Finset R) (hI : Ideal.span (s : Set R) = I)
    (hsurj : ∀ f ∈ s,
      Function.Surjective (AdicCompletion.of (Ideal.span ({f} : Set R)) M)) :
    Function.Surjective (AdicCompletion.of I M) := sorry

end AdicCompletion

namespace IsAdicComplete

/-- Lemma 10.96.8 (Stacks 090T): completeness descends along an inclusion of
finitely generated ideals. -/
@[stacks 090T "finite-generated ideal monotonicity of adic completeness"]
theorem of_le_of_fg
    {I J : Ideal R} (hIJ : I ≤ J) (hI : I.FG) (hM : IsAdicComplete J M) :
    IsAdicComplete I M := sorry

/-- Principal specialization of finite-generated ideal descent: membership of
`f` in `J` is enough to make `M` complete for the ideal spanned by `f`. -/
@[stacks 090T "principal specialization"]
theorem span_singleton_of_mem
    {J : Ideal R} {f : R} (hf : f ∈ J) (hM : IsAdicComplete J M) :
    IsAdicComplete (Ideal.span ({f} : Set R)) M := sorry

end IsAdicComplete

end
