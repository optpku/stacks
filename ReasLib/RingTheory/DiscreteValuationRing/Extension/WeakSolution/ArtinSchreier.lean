/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.FieldTheory.PurelyInseparable.PowerIntersection
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Equicharacteristic degree-`p` weak solutions

This file owns the reusable existence statement behind Lemma 15.116.12.  The source-facing
intersection is retained as a companion to the canonical `PerfectClosure.powerIntersection`
object, while the conclusion uses the field-model total-ramification predicate directly.

@stack 09F1
-/

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open DVR.Field

universe u v w x y z

namespace IsWeakSolutionFor

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M]
variable [Algebra K M] [Algebra L M] [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M] [IsScalarTower K L M]
variable [FiniteDimensional L M] [IsGalois L M]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Lemma 15.116.12 (09F1): the degree-`p` Artin--Schreier case admits a totally ramified
finite Galois weak solution.  The composite DVR extension is derived from the displayed tower,
so callers need only the two adjacent extension instances. -/
@[stacks 09F1 "Lemma 15.116.12: equicharacteristic degree-p weak solution"]
theorem exists_of_degree_p_galois
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1)
      (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsGalois K K1 ∧
        IsTotallyRamified A K K1 ∧
          IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: use the prime degree and `IsGalois L M` to choose an Artin--Schreier generator
-- of `M / L`, and choose a source uniformizer.  Normalize its parameter with a minimal pole order.
-- The power-intersection hypothesis gives compatible residue-field sections on all Artinian
-- quotients of the weakly-unramified map `A ⊆ B`; use them to remove a maximal `p`-divisible bad
-- coefficient and strictly decrease the pole measure.  The terminal integral or prime-to-`p`
-- parameter is handled by the Artin--Schreier ramification alternatives, while the prescribed
-- totally ramified extensions and weak-solution base-change/composition API assemble the resulting
-- finite Galois extension `K1` and `IsWeakSolutionFor` witness.

/-- A source-faithful form of `exists_of_degree_p_galois` using the literal intersection of all
positive `p`-power images. -/
@[stacks 09F1 "Lemma 15.116.12: literal stable power intersection view"]
theorem exists_of_degree_p_galois_of_intersection
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1)
      (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsGalois K K1 ∧
        IsTotallyRamified A K K1 ∧
          IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: rewrite the literal positive-power intersection with
-- `PerfectClosure.powerIntersection_eq` and apply `exists_of_degree_p_galois`.

/-- Downstream view with the composite DVR extension already installed as a canonical instance. -/
@[stacks 09F1 "Lemma 15.116.12: explicit composite-extension view"]
theorem exists_of_degree_p_galois_of_extension
    [IsExtensionOfDiscreteValuationRings A C]
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1)
      (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsGalois K K1 ∧
        IsTotallyRamified A K K1 ∧
          IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: apply `exists_of_degree_p_galois`; align the supplied composite DVR-extension
-- instance with `of_tower A B C` by proof irrelevance, leaving the existential witness unchanged.

end

end IsWeakSolutionFor
