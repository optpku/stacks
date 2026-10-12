/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.LocalRing

@[expose] public section

universe u v

/-- For an essentially finite type local algebra of Noetherian local rings, formal
unramifiedness is equivalent to equality of the extended maximal ideal with the target
maximal ideal and a finite-dimensional separable extension of residue fields. -/
theorem Algebra.FormallyUnramified.iff_localRingConditions
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B] :
    Algebra.FormallyUnramified A B ↔
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ∧
        (FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧
          Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := sorry

end
