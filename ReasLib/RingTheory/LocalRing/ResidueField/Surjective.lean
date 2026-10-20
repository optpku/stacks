/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue fields of surjective local maps

This file records the residue-field consequence of surjectivity for a local ring map.

@stack 0DQ1
-/

@[expose] public section

universe u v

namespace RingHom.ResidueField

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- A surjective local ring homomorphism induces a bijection on residue fields. -/
@[stacks 0DQ1 "residue fields of a surjective local map"]
theorem map_bijective_of_surjective
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  constructor
  · exact (IsLocalRing.ResidueField.map f).injective
  · intro y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := hf s
    exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.map_residue f r⟩

/-- A surjective homomorphism of commutative local rings induces a ring equivalence of
their residue fields. -/
noncomputable def mapEquivOfSurjective (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective
    (@IsLocalRing.ResidueField.map R S _ _ _ _ f (IsLocalHom.of_surjective f hf))
    (@map_bijective_of_surjective R S _ _ _ _ f (IsLocalHom.of_surjective f hf) hf)

/-- The residue-field equivalence induced by a surjection sends the residue of an
element to the residue of its image. -/
theorem mapEquivOfSurjective_apply_residue (f : R →+* S) (hf : Function.Surjective f)
    (r : R) :
    mapEquivOfSurjective f hf (IsLocalRing.residue R r) =
      IsLocalRing.residue S (f r) := sorry

/-- The inverse residue-field equivalence sends the residue of an image back to the
corresponding residue in the source. -/
theorem mapEquivOfSurjective_symm_apply_residue (f : R →+* S)
    (hf : Function.Surjective f) (r : R) :
    (mapEquivOfSurjective f hf).symm (IsLocalRing.residue S (f r)) =
      IsLocalRing.residue R r := sorry

end RingHom.ResidueField
