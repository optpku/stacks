module

public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral maps of local rings

This file records the map-level API for integral homomorphisms between local
rings.  The canonical map on residue fields remains the Mathlib owner
`IsLocalRing.ResidueField.map`; the results below state the properties it
inherits from the original map.

@stack 092X
-/

open IsLocalRing

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]

/-- The canonical residue-field map of a ring homomorphism together with an
explicit proof that it is local.  Keeping locality explicit avoids installing
a proof-local typeclass instance merely to construct the map. -/
@[stacks 092X "the residue-field map of a local homomorphism"]
noncomputable def residueFieldMap (f : R →+* S) (hlocal : IsLocalHom f) :
    ResidueField R →+* ResidueField S :=
  @IsLocalRing.ResidueField.map R S _ _ _ _ f hlocal

/-- The explicit residue-field map commutes with the two residue maps. -/
theorem residueFieldMap_comp_residue (f : R →+* S) (hlocal : IsLocalHom f) :
    (f.residueFieldMap hlocal).comp (residue R) = (residue S).comp f := sorry
-- Proof strategy: unfold `RingHom.residueFieldMap` and apply
-- `IsLocalRing.ResidueField.map_comp_residue` with the explicit locality witness.

end RingHom

namespace RingHom.IsIntegral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsLocalRing R] [IsLocalRing S]

/-- An integral homomorphism between local rings is local.  No injectivity
assumption is needed: the contraction of the target maximal ideal is the
unique maximal ideal of the source. -/
@[stacks 092X "integral homomorphisms between local rings are local"]
theorem isLocalHom_of_isLocalRing {f : R →+* S} (hf : f.IsIntegral) :
    IsLocalHom f := sorry
-- Proof strategy: contract `maximalIdeal S` along `f`, use integrality to prove the contraction
-- maximal, identify it with `maximalIdeal R`, and conclude via `IsLocalRing.local_hom_TFAE`.

/-- The residue-field map induced by an integral local homomorphism is
integral. -/
@[stacks 092X "integrality of the induced residue-field map"]
theorem residueFieldMap_isIntegral {f : R →+* S} (hf : f.IsIntegral)
    (hlocal : IsLocalHom f) :
    (f.residueFieldMap hlocal).IsIntegral := sorry
-- Proof strategy: prove the composite with `residue R` integral using integrality of `f` and
-- the target residue map, rewrite it with `residueFieldMap_comp_residue`, and descend
-- integrality through the surjective residue map using `RingHom.IsIntegral.tower_top`.

/-- If the source residue field is separably closed, the residue-field map
induced by an integral local homomorphism is purely inseparable. -/
@[stacks 092X "pure inseparability of the induced residue-field map"]
theorem residueFieldMap_isPurelyInseparable
    {f : R →+* S} [IsSepClosed (ResidueField R)]
    (hf : f.IsIntegral) (hlocal : IsLocalHom f) :
    (f.residueFieldMap hlocal).IsPurelyInseparable := sorry
-- Proof strategy: turn `hf.residueFieldMap_isIntegral hlocal` into algebraicity of the
-- residue-field extension and apply
-- `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`.

end RingHom.IsIntegral

namespace Algebra.IsIntegral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S] [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S]

/-- The residue-field extension of an integral local algebra is integral. -/
@[stacks 092X "integrality of residue-field extensions"]
theorem residueField_isIntegral :
    Algebra.IsIntegral (ResidueField R) (ResidueField S) := sorry
-- Proof strategy: apply `RingHom.IsIntegral.residueFieldMap_isIntegral` to `algebraMap R S` and
-- transport the result across the canonical residue-field algebra-map identification.

/-- The residue-field extension of an integral local algebra with separably
closed source residue field is purely inseparable. -/
@[stacks 092X "pure inseparability of residue-field extensions"]
theorem residueField_isPurelyInseparable
    [IsSepClosed (ResidueField R)] :
    IsPurelyInseparable (ResidueField R) (ResidueField S) := sorry
-- Proof strategy: specialize
-- `RingHom.IsIntegral.residueFieldMap_isPurelyInseparable` to the algebra map and identify its
-- explicit residue-field map with the canonical algebra map.

end Algebra.IsIntegral
