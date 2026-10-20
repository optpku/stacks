/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extension of Divided Powers

This module owns extension data for a divided power structure along a ring homomorphism. It is
independent of a chosen category of divided power rings.
-/

universe u v

namespace DividedPowers

/-- An extension of the divided powers `γ` along `f` is a divided power structure on the image
ideal `Ideal.map f I` for which `f` is a divided power morphism. -/
abbrev Extension {A : Type u} [CommSemiring A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommSemiring B] (f : A →+* B) :=
  { δ : DividedPowers (I.map f) // IsDPMorphism γ δ f }

/-- The divided powers `γ` extend along `f` when there are divided powers on `I.map f`
making `f` a divided power morphism. -/
@[stacks 07H0]
def extendsAlong {A : Type u} [CommSemiring A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommSemiring B] (f : A →+* B) : Prop :=
  ∃ δ : DividedPowers (I.map f), IsDPMorphism γ δ f

namespace Extension

variable {A : Type u} [CommSemiring A] {I : Ideal A} {γ : DividedPowers I}
variable {B : Type v} [CommSemiring B] {f : A →+* B}

/-- The divided power structure carried by extension data. -/
abbrev dividedPowers (h : γ.Extension f) : DividedPowers (I.map f) :=
  h.1

/-- The underlying ring map of extension data is a divided power morphism. -/
theorem isDPMorphism (h : γ.Extension f) :
    IsDPMorphism γ h.dividedPowers f := sorry

/-- Extension data are determined by their divided power structure. -/
@[ext]
theorem ext {h h' : γ.Extension f} (hδ : h.dividedPowers = h'.dividedPowers) :
    h = h' := sorry

/-- Extension data witness the corresponding extension predicate. -/
theorem extendsAlong (h : γ.Extension f) : γ.extendsAlong f := sorry

end Extension

/-- The defining expansion of `DividedPowers.extendsAlong`. -/
theorem extendsAlong_iff {A : Type u} [CommSemiring A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommSemiring B] (f : A →+* B) :
    γ.extendsAlong f ↔ ∃ δ : DividedPowers (I.map f), IsDPMorphism γ δ f := sorry

/-- The extension predicate is equivalent to the nonemptiness of extension data. -/
theorem extendsAlong_iff_nonempty_extension
    {A : Type u} [CommSemiring A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommSemiring B] (f : A →+* B) :
    γ.extendsAlong f ↔ Nonempty (γ.Extension f) := sorry

end DividedPowers
