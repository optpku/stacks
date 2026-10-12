/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace DividedPowers

/-- A divided power structure on `J ⊔ I.map f` is compatible with `gamma` and `delta` when
the induced maps from both divided power structures are divided-power morphisms. -/
def IsCompatible {A : Type u} [CommRing A] {I : Ideal A} (gamma : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (delta : DividedPowers J) (f : A →+* B) : Prop :=
  ∃ gammaBar : DividedPowers (J ⊔ I.map f),
    IsDPMorphism gamma gammaBar f ∧ IsDPMorphism delta gammaBar (RingHom.id B)

/-- The compatibility relation is equivalent to the existence of a common extension structure
with the two required divided-power morphism conditions. -/
theorem isCompatible_iff {A : Type u} [CommRing A] {I : Ideal A} (gamma : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (delta : DividedPowers J) (f : A →+* B) :
    IsCompatible gamma delta f ↔
      ∃ gammaBar : DividedPowers (J ⊔ I.map f),
        IsDPMorphism gamma gammaBar f ∧ IsDPMorphism delta gammaBar (RingHom.id B) := sorry

/-- Compatibility follows from a divided power structure on `J ⊔ I.map f` satisfying both
divided-power morphism conditions. -/
theorem isCompatible_of {A : Type u} [CommRing A] {I : Ideal A} (gamma : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (delta : DividedPowers J) (f : A →+* B)
    (gammaBar : DividedPowers (J ⊔ I.map f)) (hγ : IsDPMorphism gamma gammaBar f)
    (hδ : IsDPMorphism delta gammaBar (RingHom.id B)) : IsCompatible gamma delta f := sorry

end DividedPowers
