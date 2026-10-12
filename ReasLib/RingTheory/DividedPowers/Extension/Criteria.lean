/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DividedPowers.Extension

@[expose] public section

/-!
# Criteria for Extending Divided Powers

This module provides uniqueness of extension data and the standard zero-image, principal-ideal,
or flatness existence criterion.
-/

universe u v

namespace DividedPowers

/-- Lemma 23.4.2 (1) (Tag 07H1): extension data for divided powers along a ring homomorphism
are subsingleton. -/
@[stacks 07H1 "(1)"]
theorem subsingletonExtensions {A : Type u} [CommSemiring A] {I : Ideal A}
    (γ : DividedPowers I) {B : Type v} [CommSemiring B] (f : A →+* B) :
    Subsingleton (γ.Extension f) := sorry

/-- Extension data along a ring homomorphism are unique. -/
instance instSubsingletonExtension {A : Type u} [CommSemiring A] {I : Ideal A}
    (γ : DividedPowers I) {B : Type v} [CommSemiring B] (f : A →+* B) :
    Subsingleton (γ.Extension f) := sorry

/-- Two divided power structures on the image ideal that make the same semiring homomorphism a
divided power morphism are equal. -/
theorem eq_of_isDPMorphism_map {A : Type u} [CommSemiring A] {I : Ideal A}
    {γ : DividedPowers I} {B : Type v} [CommSemiring B] {f : A →+* B}
    {δ δ' : DividedPowers (I.map f)}
    (hδ : IsDPMorphism γ δ f) (hδ' : IsDPMorphism γ δ' f) :
    δ = δ' := sorry

/-- Divided powers extend along a ring homomorphism whose image ideal is zero. -/
theorem extendsAlong_of_map_eq_bot
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) (h : I.map f = ⊥) :
    γ.extendsAlong f := sorry

/-- Divided powers on a principal ideal extend along every ring homomorphism. -/
theorem extendsAlong_of_isPrincipal
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) (h : I.IsPrincipal) :
    γ.extendsAlong f := sorry

/-- Divided powers extend along a flat ring homomorphism. -/
theorem extendsAlong_of_flat
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) (h : f.Flat) :
    γ.extendsAlong f := sorry

/-- Lemma 23.4.2 (2) (Tag 07H1): divided powers extend along a ring homomorphism when the
image ideal is zero, the source ideal is principal, or the map is flat. -/
@[stacks 07H1 "(2)"]
theorem extendsAlong_of_map_eq_bot_or_isPrincipal_or_flat
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B)
    (h : I.map f = ⊥ ∨ I.IsPrincipal ∨ f.Flat) :
    γ.extendsAlong f := sorry

end DividedPowers
