/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace associatedPrimesOfModule.Adic

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable {M : Type x} [AddCommGroup M] [Module R M]

/-- If `N` is `I`-adically complete, then every exact associated prime of `N ⊗[R] M`
remains proper after adding the extension of `I` to `S`. -/
theorem add_map_ne_top (I : Ideal R) [IsAdicComplete I N] {q : Ideal S}
    (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    q + I.map (algebraMap R S) ≠ ⊤ := sorry

end associatedPrimesOfModule.Adic
