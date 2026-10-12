/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Localization
public import ReasLib.RingTheory.EssentialFiniteness.Basic

@[expose] public section

/-!
# Catenarity of Finite-Type Algebras

This leaf gives the finite-type and essentially-finite-type closure API for
universal catenarity, including the canonical localization comparison attached
to an essentially finite type algebra.
-/

universe u v w

section

variable (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A finite type algebra over a universally catenary ring is universally catenary. -/
@[stacks 0ECE "finite type universal catenarity"]
theorem universallyCatenaryRing_of_finiteType {S : Type v} [CommRing S] [Algebra A S]
    [UniversallyCatenaryRing.{u, w} A] [Algebra.FiniteType A S] :
    UniversallyCatenaryRing.{v, w} S := sorry

/-- The canonical localization witness for an essentially finite type algebra is ring-equivalent
to the target algebra. -/
@[stacks 0ECE "canonical localization witness"]
noncomputable def essFiniteType_witness_localization_ringEquiv [Algebra.EssFiniteType A B] :
    Localization (Algebra.EssFiniteType.submonoid A B) ≃+* B :=
  (IsLocalization.algEquiv (Algebra.EssFiniteType.submonoid A B)
    (Localization (Algebra.EssFiniteType.submonoid A B)) B).toRingEquiv

/-- An essentially finite type algebra over a universally catenary ring is universally
catenary. -/
@[stacks 0ECE]
theorem universallyCatenaryRing_of_essFiniteType [UniversallyCatenaryRing.{u, w} A]
    [Algebra.EssFiniteType A B] : UniversallyCatenaryRing.{v, w} B := sorry

end
