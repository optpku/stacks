module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped.Tensor
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Contraction from a flat prime quotient

For a prime `p` of the base and an `R`-flat `S`-module `N`, every exact associated prime of
`N / pN` contracts to `p`.  The statement is ideal-level: the primality of the target ideal is
already a consequence of associated-prime membership and is not duplicated as an input instance.

@stack 05C2
-/

@[expose] public section

universe u v w

namespace associatedPrimesOfModule.BaseChange.Flat

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- An exact associated prime of `N / pN` contracts to `p` when `N` is flat over the base. -/
@[stacks 05C2 "contraction from a flat prime quotient"]
theorem under_eq_of_mem_quotient [Module.Flat R N]
    {p : Ideal R} [p.IsPrime] {q : Ideal S}
    (hq : q ∈ associatedPrimesOfModule S
      (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) :
    q.under R = p := sorry

end associatedPrimesOfModule.BaseChange.Flat
