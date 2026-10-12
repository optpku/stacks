/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotients of Local Homomorphisms

@stack 05WQ

This leaf owns the locality of the ring map induced by compatible quotients.
The Jacobson-radical form is the primitive result: it does not require either
ambient ring to be local.  The proper-ideal form is the local-ring convenience
specialization.
-/

universe u v

namespace IsLocalHom

/-- A local homomorphism descends through compatible quotients when the target
ideal lies in the Jacobson radical. -/
@[stacks 05WQ "local homomorphism quotient over a Jacobson ideal"]
theorem quotient_of_le_jacobson
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} [IsLocalHom f] {I : Ideal R} {J : Ideal S}
    (hIJ : I ≤ Ideal.comap f J) (hJ : J ≤ Ring.jacobson S) :
    IsLocalHom (Ideal.quotientMap J f hIJ) := by
  refine ⟨?_⟩
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : IsUnit (Ideal.Quotient.mk J (f r)) := by
    simpa using hx
  obtain ⟨u, hu⟩ := hx'
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (S ⧸ J)ˣ) : S ⧸ J)
  have hrs : f r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, map_mul, map_one, ← hu, hs]
    simp
  have hrsJac : f r * s - 1 ∈ Ideal.jacobson (⊥ : Ideal S) := by
    rw [Ideal.jacobson_bot]
    exact hJ hrs
  have hfrs : IsUnit (f r * s) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot (f r * s) hrsJac
  have hfr : IsUnit (f r) := isUnit_of_mul_isUnit_left hfrs
  exact (IsLocalHom.map_nonunit r hfr).map (Ideal.Quotient.mk I)

/-- A local homomorphism descends through compatible proper quotients of a
local target ring. -/
@[stacks 05WQ "local homomorphism quotient over a proper ideal"]
theorem quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing S]
    {f : R →+* S} [IsLocalHom f] {I : Ideal R} {J : Ideal S}
    (hIJ : I ≤ Ideal.comap f J) (hJ : J ≠ ⊤) :
    IsLocalHom (Ideal.quotientMap J f hIJ) :=
  quotient_of_le_jacobson hIJ <| by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.le_maximalIdeal hJ

end IsLocalHom
