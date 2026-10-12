/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Instances

/-!
# Local Properties of Commutative Rings

This leaf packages the principal-open finite-cover criterion for a property of
commutative rings.  It is the natural ring-level input for affine-local
properties of schemes.
-/

@[expose] public section

universe u

/-- A property `P` of commutative rings is local if it is preserved by localization at one
element and descends from a finite principal-open cover. -/
class RingPropertyIsLocal (P : CommRingCat.{u} → Prop) : Prop where
  /-- The property is preserved by principal localizations. -/
  away : ∀ (R : CommRingCat.{u}) (f : R),
    P R → P (CommRingCat.of (Localization.Away f))
  /-- The property descends from finitely many principal localizations spanning the unit ideal. -/
  ofSpanEqTop : ∀ (R : CommRingCat.{u}) (s : Finset R),
    Ideal.span (s : Set R) = ⊤ →
      (∀ f ∈ s, P (CommRingCat.of (Localization.Away f))) → P R

/-- Unfold `RingPropertyIsLocal` into preservation by principal localizations and descent from a
finite principal-open cover. -/
theorem ringPropertyIsLocal_iff (P : CommRingCat.{u} → Prop) :
    RingPropertyIsLocal P ↔
      (∀ (R : CommRingCat.{u}) (f : R),
        P R → P (CommRingCat.of (Localization.Away f))) ∧
      (∀ (R : CommRingCat.{u}) (s : Finset R),
        Ideal.span (s : Set R) = ⊤ →
          (∀ f ∈ s, P (CommRingCat.of (Localization.Away f))) → P R) := sorry
