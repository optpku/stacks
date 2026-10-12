/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Catenary

@[expose] public section

/-!
# Catenary Rings

Ring catenarity is catenarity of the prime spectrum and is invariant under
ring equivalence.
-/

universe u v

section

variable {R : Type u} [CommRing R]

/-- A commutative ring is catenary when its prime spectrum is a catenary topological space. -/
abbrev IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  TopologicalSpace.CatenarySpace (PrimeSpectrum R)

/-- The ring-level catenarity condition is catenarity of `PrimeSpectrum R`. -/
@[stacks 02IH]
theorem isCatenaryRing_iff_catenarySpace_primeSpectrum :
    IsCatenaryRing R ↔ TopologicalSpace.CatenarySpace (PrimeSpectrum R) := sorry

/-- Catenarity transports across ring equivalences. -/
theorem isCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := sorry

end
