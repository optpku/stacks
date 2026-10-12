/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Flatness.MittagLeffler.Pi
import ReasLib.RingTheory.Flatness.MittagLeffler.Exact

/-!
# Adic completions of free modules of arbitrary rank

This leaf owns the canonical comparison from the completion of a direct sum to the corresponding
product.  It also records universal injectivity over a complete Noetherian ring and flatness of the
completed direct sum over an arbitrary Noetherian ring.

@stack 05BC
@stack 06LE
-/

@[expose] public section

open scoped DirectSum

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The canonical map from the `I`-adic completion of `⨁ a : A, R` to `A → R` when
`R` is `I`-adically complete. -/
@[stacks 05BC "Lemma 15.27.1"]
noncomputable abbrev directSumToPi (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] A → R :=
  ((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
    (((pi I (fun _ : A ↦ R)).restrictScalars R).comp
      ((map I (DirectSum.coeFnLinearMap R)).restrictScalars R))

/-- The direct-sum comparison extends the ordinary inclusion into the product. -/
@[simp, stacks 05BC "Lemma 15.27.1"]
theorem directSumToPi_of (I : Ideal R) [IsAdicComplete I R] (A : Type v)
    (x : ⨁ _ : A, R) :
    directSumToPi I A (of I (⨁ _ : A, R) x) = DirectSum.coeFnLinearMap R x := sorry

/-- Composing the direct-sum comparison with the dense map recovers the ordinary inclusion. -/
@[simp, stacks 05BC "Lemma 15.27.1"]
theorem directSumToPi_comp_of (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    (directSumToPi I A).comp (of I (⨁ _ : A, R)) = DirectSum.coeFnLinearMap R := sorry

/-- Over a Noetherian ring complete along `I`, the canonical map from the completion of
`⨁ a : A, R` to `A → R` is universally injective. -/
@[stacks 05BC "Lemma 15.27.1"]
theorem directSumToPi_universallyInjective
    (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] (A : Type v) :
    (directSumToPi I A).UniversallyInjective := sorry

/-- Over a Noetherian ring, the `I`-adic completion of the free module `⨁ a : A, R`
is flat. -/
@[stacks 06LE "Lemma 15.27.2"]
theorem directSum_flat (I : Ideal R) [IsNoetherianRing R] (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := sorry

end AdicCompletion

namespace Module.Flat

variable {R : Type u} [CommRing R]

/-- Over a Noetherian ring complete along `I`, the `I`-adic completion of a direct sum
of copies of the ring is flat. -/
@[stacks 05DJ]
instance adicCompletionDirectSum (I : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete I R] (A : Type v) :
    Module.Flat R (AdicCompletion I (⨁ _ : A, R)) := sorry

end Module.Flat

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]

/-- Over a Noetherian ring complete along `I`, the `I`-adic completion of a direct sum
of copies of the ring is Mittag-Leffler. -/
@[stacks 05DJ]
instance adicCompletionDirectSum (I : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete I R] (A : Type v) :
    Module.MittagLeffler R (AdicCompletion I (⨁ _ : A, R)) := sorry

end Module.MittagLeffler
