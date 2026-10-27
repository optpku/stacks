/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.DividedPowers.Extension.Criteria

@[expose] public section
noncomputable section
universe u v
namespace DividedPowers
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)

/-- Unique divided-power extension of `γA` along a ring map, when an extension exists. -/
def extensionAlong {B : Type v} [CommRing B] (f : A →+* B)
    (h : γA.extendsAlong f) : γA.Extension f :=
  Classical.choice
    ((DividedPowers.extendsAlong_iff_nonempty_extension γA f).mp h)

/-- The chosen extension is a divided-power morphism along `f`. -/
theorem extensionAlong_spec {B : Type v} [CommRing B] (f : A →+* B)
    (h : γA.extendsAlong f) :
    DividedPowers.IsDPMorphism γA (extensionAlong γA f h).dividedPowers f :=
  sorry

/-- Transport divided powers along an equality of ideals. -/
def dividedPowers_ofIdealEq {R : Type u} [CommSemiring R] {J K : Ideal R}
    (h : J = K) (γ : DividedPowers J) : DividedPowers K :=
  h ▸ γ


end DividedPowers
