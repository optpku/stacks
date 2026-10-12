/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.DividedPowers.Category.Quotient

@[expose] public section

universe u v w

/-- The implementation record carrying the data of a divided-power thickening. -/
structure DividedPowerThickeningData
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (C : Type v) [CommRing C] (f : A →+* C)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C)) where
  B : DividedPowerRing.{w}
  base : DividedPowers.DPMorphism γ B.dividedPowers
  p_nilpotent : IsNilpotent (p : B)
  quotient : C →+* (B ⧸ B.ideal)
  commutative :
    (Ideal.Quotient.mk B.ideal).comp base.toRingHom = quotient.comp f

/-- A divided-power thickening of a crystalline base, with its ring, base map,
nilpotence condition, quotient map, and commutative quotient square. -/
def DividedPowerThickening
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (C : Type v) [CommRing C] (f : A →+* C)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C)) :=
  DividedPowerThickeningData p A I γ C f hIC h_pC

namespace DividedPowerThickening

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-- The underlying bundled divided-power ring of a thickening. -/
def B (T : DividedPowerThickening p A I γ C f hIC h_pC) : DividedPowerRing :=
  DividedPowerThickeningData.B T

/-- The divided-power morphism from the base ring into a thickening. -/
def base (T : DividedPowerThickening p A I γ C f hIC h_pC) :
    DividedPowers.DPMorphism γ T.B.dividedPowers :=
  DividedPowerThickeningData.base T

/-- The nilpotence condition on the chosen prime in a thickening. -/
def p_nilpotent (T : DividedPowerThickening p A I γ C f hIC h_pC) :
    IsNilpotent (p : T.B) :=
  DividedPowerThickeningData.p_nilpotent T

/-- The map from the base algebra to the quotient of a thickening. -/
def quotient (T : DividedPowerThickening p A I γ C f hIC h_pC) :
    C →+* (T.B ⧸ T.B.ideal) :=
  DividedPowerThickeningData.quotient T

/-- The commutative square relating the base and quotient maps. -/
def commutative (T : DividedPowerThickening p A I γ C f hIC h_pC) :
    (Ideal.Quotient.mk T.B.ideal).comp T.base.toRingHom = T.quotient.comp f :=
  DividedPowerThickeningData.commutative T

/-- Construct a thickening from its explicit divided-power ring and structure maps. -/
def of (B : DividedPowerRing.{w})
    (base : DividedPowers.DPMorphism γ B.dividedPowers)
    (p_nilpotent : IsNilpotent (p : B))
    (quotient : C →+* (B ⧸ B.ideal))
    (commutative :
      (Ideal.Quotient.mk B.ideal).comp base.toRingHom = quotient.comp f) :
    DividedPowerThickening p A I γ C f hIC h_pC :=
  DividedPowerThickeningData.mk B base p_nilpotent quotient commutative

/-- The nilpotence and quotient-square conditions of a thickening. -/
theorem spec (T : DividedPowerThickening p A I γ C f hIC h_pC) :
    IsNilpotent (p : T.B) ∧
      (Ideal.Quotient.mk T.B.ideal).comp T.base.toRingHom = T.quotient.comp f := sorry

end DividedPowerThickening
