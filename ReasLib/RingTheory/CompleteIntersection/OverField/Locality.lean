/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Localization
public import ReasLib.RingTheory.CompleteIntersection.OverField.Comparison
public import ReasLib.RingTheory.CompleteIntersection.OverField

@[expose] public section

/-!
# Locality for Complete Intersections over a Field

This leaf records the elementary transport and finite principal-open gluing
principles for `IsLocalCompleteIntersection`.  They belong to the owner
predicate rather than to a later application such as syntomicity.
-/

universe u v w

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

section FiniteType

variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- Lemma 10.135.9 (00SH): a finite-type algebra over a field is a local complete
intersection exactly when all of its prime localizations are complete intersections over the
base field. -/
@[stacks 00SH "local complete intersections detected at prime localizations"]
theorem iff_forall_prime :
    IsLocalCompleteIntersection k S ↔
      ∀ q : PrimeSpectrum S,
        Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) := sorry

/-- Lemma 10.135.9 (00SH): a finite-type algebra over a field is a local complete
intersection exactly when all of its maximal localizations are complete intersections over the
base field. -/
@[stacks 00SH "local complete intersections detected at maximal localizations"]
theorem iff_forall_maximal :
    IsLocalCompleteIntersection k S ↔
      ∀ m : MaximalSpectrum S,
        Algebra.IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal) := sorry

end FiniteType

/-- Lemma 10.136.4: local complete intersections are invariant under
equivalences of `k`-algebras. -/
@[stacks 00SO "local complete intersections and algebra equivalences"]
theorem of_algEquiv {B : Type w} [CommRing B] [Algebra k B]
    (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := sorry

/-- Lemma 10.136.4: a finite principal-open cover by local complete
intersections makes the target a local complete intersection. -/
@[stacks 00SO "local complete intersections glue on principal opens"]
theorem of_span_eq_top (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤)
    (hloc : ∀ g : s, IsLocalCompleteIntersection k (Localization.Away (g : A))) :
    IsLocalCompleteIntersection k A := sorry

end IsLocalCompleteIntersection
