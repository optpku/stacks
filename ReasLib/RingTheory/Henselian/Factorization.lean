module

public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization criterion for henselian pairs

@stack 09XE

This leaf exposes the two source-facing clauses of a henselian pair: containment in the ring's
Jacobson radical and lifting monic coprime factorizations modulo the henselian ideal.
-/

@[expose] public section

open Polynomial

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- Definition 15.11.1 (1): the ideal of a henselian pair is contained in the Jacobson radical. -/
@[stacks 09XE "Definition 15.11.1 (1), Jacobson-radical clause"]
theorem le_ring_jacobson_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    I ≤ Ring.jacobson A := sorry

/-- Definition 15.11.1 (Stacks `09XE`), factorization clause: a henselian ideal lifts monic
coprime factorizations modulo the ideal. -/
@[stacks 09XE "Definition 15.11.1 (2), monic coprime factorization lifting"]
theorem exists_monic_coprime_factorization_lift (I : Ideal A) [HenselianRing A I]
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧
          h.map (Ideal.Quotient.mk I) = h₀ := sorry

end Ideal
