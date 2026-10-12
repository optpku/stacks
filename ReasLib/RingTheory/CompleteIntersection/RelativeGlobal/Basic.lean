/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
intersection presentation when the number of relations is at most the number
of generators and every nonempty fiber has the expected Krull dimension. -/
@[stacks 00SP "relative global complete intersection presentation"]
def IsRelativeGlobalCompleteIntersection (P : Algebra.Presentation R S (Fin n) (Fin c)) : Prop :=
  c ≤ n ∧
    ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) →
        ringKrullDim (p.asIdeal.Fiber S) = P.dimension

/-- The relation count of a relative global complete intersection presentation
does not exceed its generator count. -/
theorem IsRelativeGlobalCompleteIntersection.card_relations_le
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) : c ≤ n := sorry

/-- Every nonempty fiber of a relative global complete intersection presentation
has the presentation's expected Krull dimension. -/
theorem IsRelativeGlobalCompleteIntersection.ringKrullDim_fiber
    {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S))) :
    ringKrullDim (p.asIdeal.Fiber S) = P.dimension := sorry

end Presentation

/-- An `R`-algebra `S` is a relative global complete intersection when it
admits a finite presentation whose relation count is at most its generator
count and whose nonempty fibers have the expected Krull dimension. -/
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
    Algebra.IsRelativeGlobalCompleteIntersection R S := sorry

/-- A relative global complete intersection algebra is finitely presented over
its base ring. -/
instance instFinitePresentationOfIsRelativeGlobalCompleteIntersection
    [h : IsRelativeGlobalCompleteIntersection R S] : Algebra.FinitePresentation R S := sorry

end

end Algebra
