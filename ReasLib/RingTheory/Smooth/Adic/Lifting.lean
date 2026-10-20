module

public import Mathlib.Data.PNat.Notation
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-!
# Lifting for adically formally smooth maps

@stack 07NJ
-/

@[expose] public section

open scoped Topology

universe u v w

namespace RingHom

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Lemma 15.37.5: an adically formally smooth map admits continuous lifts to a complete
separated target under the stated ideal-theoretic hypotheses. -/
@[stacks 07NJ "adic formal smoothness lifting theorem"]
theorem exists_continuous_lift_of_formally_smooth_for_adic
    (f : R →+* S) (𝔫 : Ideal S) (hf : formally_smooth_for_adic f 𝔫) (hS : IsAdic 𝔫)
    (I J : Ideal A) (hA : IsAdic I) [IsAdicComplete I A]
    (hJClosed : IsClosed (J : Set A))
    (hpow : ∃ t : ℕ+, J ^ (t : ℕ) ≤ I)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (g : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g = ψ.comp f) :
    ∃ φ : S →+* A, (Ideal.Quotient.mk J).comp φ = ψ ∧ φ.comp f = g ∧ Continuous φ := sorry

end

end RingHom
