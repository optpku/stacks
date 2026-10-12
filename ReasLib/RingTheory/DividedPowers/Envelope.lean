/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.DividedPowers.Category

@[expose] public section

open CategoryTheory

universe u

/-- A relative divided-power envelope diagram for `I` along `f`, with quotient ideal `J`.

The carrier `D` and all maps are explicit data; the remaining fields record the compatibility
conditions needed for the diagram `B ⟶ D ⟶ B ⧸ J`. -/
structure DividedPowerEnvelope {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (gamma : DividedPowers I) (f : A →+* B)
    (J : Ideal B) (hIJ : Ideal.map f I ≤ J) where
  /-- The divided-power ring serving as the envelope. -/
  D : DividedPowerRing.{u}
  /-- The divided-power morphism from the base ring to the envelope. -/
  base : DividedPowers.DPMorphism gamma D.dividedPowers
  /-- The ring homomorphism from `B` to the envelope ring `D`. -/
  toD : B →+* D
  /-- The ring homomorphism from the envelope ring to the quotient `B ⧸ J`. -/
  toQuotient : D →+* (B ⧸ J)
  /-- The base divided-power morphism has underlying map `toD.comp f`. -/
  base_toD : base.toRingHom = toD.comp f
  /-- The image of `J` under `toD` is contained in the distinguished ideal of `D`. -/
  ideal_map : Ideal.map toD J ≤ D.ideal
  /-- The composite through `D` is the canonical quotient map. -/
  quotient_comp : toQuotient.comp toD = Ideal.Quotient.mk J

namespace DividedPowerEnvelope

variable {A B : Type u} [CommRing A] [CommRing B]
  {I : Ideal A} (gamma : DividedPowers I) (f : A →+* B)
  {J : Ideal B} (hIJ : Ideal.map f I ≤ J)

/-- Compatible base and quotient maps construct a relative divided-power envelope diagram. -/
def ofMaps (D : DividedPowerRing.{u}) (base : DividedPowers.DPMorphism gamma D.dividedPowers)
    (toD : B →+* D) (toQuotient : D →+* (B ⧸ J))
    (base_toD : base.toRingHom = toD.comp f) (ideal_map : Ideal.map toD J ≤ D.ideal)
    (quotient_comp : toQuotient.comp toD = Ideal.Quotient.mk J) :
    DividedPowerEnvelope I gamma f J hIJ where
  D := D
  base := base
  toD := toD
  toQuotient := toQuotient
  base_toD := base_toD
  ideal_map := ideal_map
  quotient_comp := quotient_comp

/-- The composable-arrows view of an envelope is the chain `B ⟶ D ⟶ B ⧸ J`. -/
def sequence (E : DividedPowerEnvelope I gamma f J hIJ) :
    ComposableArrows CommRingCat 2 :=
  ComposableArrows.mk₂ (CommRingCat.ofHom E.toD) (CommRingCat.ofHom E.toQuotient)

/-- The composite map of the envelope sequence is the canonical quotient map `B ⟶ B ⧸ J`. -/
theorem sequence_hom_eq (E : DividedPowerEnvelope I gamma f J hIJ) :
    E.sequence.hom = CommRingCat.ofHom (Ideal.Quotient.mk J) := sorry

/-- The base compatibility and ideal-containment specifications of an envelope. -/
theorem base_spec (E : DividedPowerEnvelope I gamma f J hIJ) :
    (E.base.toRingHom = E.toD.comp f) ∧ (Ideal.map E.toD J ≤ E.D.ideal) := sorry

/-- The quotient-map specification of an envelope. -/
theorem quotient_spec (E : DividedPowerEnvelope I gamma f J hIJ) :
    E.toQuotient.comp E.toD = Ideal.Quotient.mk J := sorry

end DividedPowerEnvelope
