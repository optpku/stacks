/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobson products of fields

The generic criterion is stated independently of products: a ring is Jacobson when every
principal localization map is surjective. The product-of-fields instance is the source-facing
application.

@stack 02CC
-/

@[expose] public section

universe u v

namespace IsJacobsonRing

/-- A ring is Jacobson if every canonical map to an away localization is surjective. -/
@[stacks 02CC "away-localization criterion"]
theorem of_away_algebraMap_surjective
    {R : Type u} [CommRing R]
    (h : ∀ f : R, Function.Surjective (algebraMap R (Localization.Away f))) :
    IsJacobsonRing R := sorry

end IsJacobsonRing

namespace Pi

/-- An infinite product of fields is a Jacobson ring. -/
@[stacks 02CC "infinite product of fields"]
instance instIsJacobsonRingOfInfinite
    {A : Type u} (k : A → Type v) [∀ a, Field (k a)] [Infinite A] :
    IsJacobsonRing ((a : A) → k a) := sorry

end Pi
