module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat.AdicIdealFiltration

/-- The zero-ideal filtration of an Artinian complete local algebra. -/
noncomputable def zero (R : CompleteLocalAlgCat Λ k) [IsArtinianRing R.carrier] :
    AdicIdealFiltration R where
  ideal := fun _ ↦ ⊥
  antitone := fun _ _ _ ↦ le_rfl
  le_maximal := fun _ ↦ bot_le
  exists_le_pow := fun _ ↦ ⟨0, bot_le⟩
  exists_pow_le := fun _ ↦
    Exists.elim
      ((@isArtinianRing_iff_isNilpotent_maximalIdeal R.carrier R.carrier.commRing
        R.isNoetherianRing R.isLocalRing).mp inferInstance)
      (fun k hk ↦
        ⟨k, (Ideal.pow_le_pow_right (Nat.le_succ k)).trans (le_of_eq hk)⟩)

/-- Every stage of the zero filtration is the zero ideal. -/
theorem zero_ideal (R : CompleteLocalAlgCat Λ k) [IsArtinianRing R.carrier] (n : ℕ) :
    (zero R).ideal n = ⊥ := sorry

end CompleteLocalAlgCat.AdicIdealFiltration
