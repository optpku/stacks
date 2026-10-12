/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Adic
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w x

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable {M : Type x} [AddCommGroup M] [Module R M]

/- Lemma 38.14.2: if `N` is `I`-adically complete, then every exact associated prime
of `N ⊗[R] M` remains proper after adding the extension of `I` to `S`. -/
@[stacks 05IT] #check
  (associatedPrimesOfModule.Adic.add_map_ne_top :
    ∀ (I : Ideal R) [IsAdicComplete I N] {q : Ideal S},
      q ∈ associatedPrimesOfModule S (N ⊗[R] M) →
        q + I.map (algebraMap R S) ≠ ⊤)
