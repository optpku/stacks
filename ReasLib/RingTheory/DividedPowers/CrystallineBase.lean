/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

universe u v

namespace DividedPowers

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- A divided-power ideal map is a crystalline base when it is annihilated by the map and
the image of the chosen prime is nilpotent in the target. -/
def IsCrystallineBase (p : ℕ) [Fact (Nat.Prime p)] (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    {C : Type v} [CommRing C] (f : A →+* C) : Prop :=
  Ideal.map f I = (⊥ : Ideal C) ∧ IsNilpotent (p : C)

/-- The crystalline-base condition is equivalent to containment of the divided-power ideal in
the kernel of the structure map together with nilpotence of the chosen prime. -/
theorem isCrystallineBase_iff (p : ℕ) [Fact (Nat.Prime p)] (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    {C : Type v} [CommRing C] (f : A →+* C) :
    IsCrystallineBase p γ f ↔ I ≤ RingHom.ker f ∧ IsNilpotent (p : C) := sorry

end DividedPowers
