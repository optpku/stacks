module

public import ReasLib.Algebra.Module.IdealPower.Predicate

@[expose] public section

universe u

namespace RingHom.Cokernel

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The additive cokernel of a ring homomorphism is annihilated by a power of `I` when
one power of `I` sends every target element into the additive range of the homomorphism. -/
def IsAnnihilatedByPower (I : Ideal R) (f : R →+* S) : Prop :=
  ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ y, ∃ x, f x = f a * y

variable [Algebra R S]

/-- For an algebra map, ideal-power annihilation of its additive cokernel agrees with
ideal-power annihilation of the quotient by the range of its underlying linear map. -/
theorem isAnnihilatedByPower_algebraMap_iff (I : Ideal R) :
    IsAnnihilatedByPower I (algebraMap R S) ↔
      Module.IsAnnihilatedByPower I (S ⧸ (Algebra.linearMap R S).range) := sorry

end RingHom.Cokernel

end
