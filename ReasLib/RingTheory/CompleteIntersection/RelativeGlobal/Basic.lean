/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative Global Complete Intersections

This module owns the presentation-level and intrinsic definitions of relative
global complete intersections.
-/

universe u v

namespace Algebra

namespace Presentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n c : ℕ}

/-- A finite presentation `P : R[x₁, ..., xₙ] ⟶ S` is a relative global complete
intersection presentation when every nonempty fiber has the expected Krull
dimension and the number of relations is at most the number of generators.
Empty fibers impose neither condition; the bound guards against truncated
natural-number subtraction in `P.dimension`. -/
@[stacks 00SP "relative global complete intersection presentation"]
def IsRelativeGlobalCompleteIntersection (P : Algebra.Presentation R S (Fin n) (Fin c)) : Prop :=
  ∀ p : PrimeSpectrum R,
    Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) →
      c ≤ n ∧ ringKrullDim (p.asIdeal.Fiber S) = P.dimension

/-- The relation count of a relative global complete intersection presentation
does not exceed its generator count if it has a nonempty fiber. -/
theorem IsRelativeGlobalCompleteIntersection.card_relations_le
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S))) : c ≤ n :=
  (hP p hp).1

/-- Every nonempty fiber of a relative global complete intersection presentation
has the presentation's expected Krull dimension. -/
theorem IsRelativeGlobalCompleteIntersection.ringKrullDim_fiber
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S))) :
    ringKrullDim (p.asIdeal.Fiber S) = P.dimension :=
  (hP p hp).2

end Presentation

/-- An `R`-algebra `S` is a relative global complete intersection when it
admits a finite presentation whose nonempty fibers have the expected Krull
dimension and force its relation count to be at most its generator count. -/
@[stacks 00SP]
class IsRelativeGlobalCompleteIntersection (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] : Prop where
  /-- A finite presentation satisfying the relative global complete intersection condition. -/
  exists_presentation :
    ∃ (n c : ℕ) (P : Algebra.Presentation R S (Fin n) (Fin c)),
      P.IsRelativeGlobalCompleteIntersection

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A presentation-level relative global complete intersection witness induces
the intrinsic relative global complete intersection property. -/
theorem Presentation.toIsRelativeGlobalCompleteIntersection
    {n c : ℕ} {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Algebra.IsRelativeGlobalCompleteIntersection R S :=
  ⟨⟨n, c, P, hP⟩⟩

/-- A relative global complete intersection algebra is finitely presented over
its base ring. -/
instance instFinitePresentationOfIsRelativeGlobalCompleteIntersection
    [h : IsRelativeGlobalCompleteIntersection R S] : Algebra.FinitePresentation R S := by
  obtain ⟨n, c, P, _⟩ := h.exists_presentation
  exact P.finitePresentation_of_isFinite

end

end Algebra
