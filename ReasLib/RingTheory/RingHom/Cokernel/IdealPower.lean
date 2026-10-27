/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Predicate

@[expose] public section

universe u

namespace RingHom.Cokernel

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The additive cokernel of a ring homomorphism is annihilated by a power of `I` when
one power of `I` sends every target element into the additive range of the homomorphism.

This is an elementwise specialization of `Module.IsAnnihilatedByPower`;
`isAnnihilatedByPower_iff` identifies it with that predicate on the cokernel,
with scalar action induced by the homomorphism. -/
def IsAnnihilatedByPower (I : Ideal R) (f : R →+* S) : Prop :=
  ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ y, ∃ x, f x = f a * y

/-- For any ring homomorphism, ideal-power annihilation of its additive cokernel agrees
with `Module.IsAnnihilatedByPower` on the quotient by its linear range, using the
algebra structure induced by the homomorphism. -/
theorem isAnnihilatedByPower_iff (I : Ideal R) (f : R →+* S) :
    IsAnnihilatedByPower I f ↔
      letI := f.toAlgebra
      Module.IsAnnihilatedByPower I (S ⧸ (Algebra.linearMap R S).range) := by
  letI := f.toAlgebra
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro a ha
    rw [Module.mem_annihilator]
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro s
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    exact hn a ha s
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro a ha y
    have h := Module.mem_annihilator.mp (hn ha) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h
    exact h

variable [Algebra R S]

/-- For an algebra map, ideal-power annihilation of its additive cokernel agrees with
ideal-power annihilation of the quotient by the range of its underlying linear map. -/
theorem isAnnihilatedByPower_algebraMap_iff (I : Ideal R) :
    IsAnnihilatedByPower I (algebraMap R S) ↔
      Module.IsAnnihilatedByPower I (S ⧸ (Algebra.linearMap R S).range) := sorry

end RingHom.Cokernel

end
