/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.AdicCompletion
import StacksCheckRecall

@[expose] public section

open IsLocalRing
open scoped ENat

universe u v

namespace Module.LocalCohomology

/- Lemma 51.11.4 (1): completion at the maximal ideal cannot increase the
local-cohomology finiteness cutoff. -/
@[stacks 0BJT]
#check (Module.LocalCohomology.cutoff_adicCompletion_le :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M],
      cutoff (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
        (AdicCompletion (maximalIdeal A) M) ≤ cutoff I M)

/- Lemma 51.11.4 (2): if every formal fiber satisfies `S_n`, the completed
local-cohomology finiteness cutoff is at least the minimum of `n + 1` and the
original cutoff. -/
@[stacks 0BJT]
#check (Module.LocalCohomology.min_le_cutoff_adicCompletion_of_formalFibers :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [UniversallyCatenaryRing.{u, u} A]
      (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (n : ℕ) (h_formal : (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers A),
      min ((n + 1 : ℕ) : WithBot ℕ∞) (cutoff I M) ≤
      cutoff (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
        (AdicCompletion (maximalIdeal A) M))

end Module.LocalCohomology
