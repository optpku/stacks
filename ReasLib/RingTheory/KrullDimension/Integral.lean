/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Krull Dimension of Integral Ring Maps

This file records the invariance of ring Krull dimension under injective integral maps.  The
primary statement is formulated for an explicit `RingHom`; the algebra-map form is retained as
an ergonomic companion for the common typeclass-driven use case.
-/

universe u v

namespace RingHom.IsIntegral

/-- An integral homomorphism of commutative rings does not increase ring Krull dimension. -/
@[stacks 00OJ "map-level integral dimension inequality"]
theorem ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (h_integral : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := sorry

/-- An injective integral homomorphism of commutative rings preserves ring Krull dimension. -/
@[stacks 00OK "map-level integral dimension equality"]
theorem ringKrullDim_eq_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (h_integral : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R = ringKrullDim S := sorry

end RingHom.IsIntegral

/-- An integral algebra over a commutative ring does not increase ring Krull dimension.

This is the algebra-map companion to `RingHom.IsIntegral.ringKrullDim_le`. -/
@[stacks 00OJ "(1)"]
theorem ringKrullDim_le_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := sorry

/-- If the algebra map of an integral algebra is injective, the base and extension have equal
ring Krull dimension.

This is the typeclass-oriented companion to
`RingHom.IsIntegral.ringKrullDim_eq_of_injective`. -/
@[stacks 00OK]
theorem ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := sorry
