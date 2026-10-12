/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap93.Lemma_93_12_4_AdicCompletion
public import stacks_project.Chap93.Lemma_93_12_4_Exal

/-!
# Completing first-order extensions of a finite type algebra over a field

If `k → B` is of finite type and smooth away from `V(J)`, J-adic completion
induces a bijection on first-order square-zero extensions `Exal_k(B, N)`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra
open PrimeSpectrum

namespace Algebra.Exal

variable (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module B N]

/-- Smoothness of `Spec B → Spec k` on the complement of `V(J)` is smoothness
of each principal localization `B_g` for `g ∈ J`. -/
theorem isSmoothAwayFrom_iff [Algebra.FinitePresentation k B] (J : Ideal B) :
    (zeroLocus (J : Set B))ᶜ ⊆ smoothLocus k B ↔
      ∀ g ∈ J, Algebra.Smooth k (Localization.Away (g : B)) := sorry

/-- J-adic completion of first-order extensions of a finite type algebra over a field. -/
def adicCompletionOfFiniteType [Algebra.FiniteType k B] [Module.Finite B N] (J : Ideal B) :
    Exal k B N → Exal k (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): finite type over a field supplies the Noetherian hypothesis of `Exal.adicCompletion`; `k` is not determined from `B`, so this cannot be a global instance.
  letI := Algebra.FiniteType.isNoetherianRing k B
  adicCompletion k B N J

/-- Lemma 93.12.4
Let `k` be a field. Let `B` be a finite type `k`-algebra. Let `J ⊂ B` be an
ideal such that `Spec B → Spec k` is smooth on the complement of `V(J)`. Let
`N` be a finite `B`-module. Then J-adic completion induces a canonical
bijection `Exal k B N → Exal k (AdicCompletion J B) (AdicCompletion J N)`.
-/
@[stacks 0DZ4]
theorem adicCompletion_bijective [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B) (hsmooth : (zeroLocus (J : Set B))ᶜ ⊆ smoothLocus k B) :
    Function.Bijective (adicCompletionOfFiniteType k B N J) := sorry

end Algebra.Exal
