/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import ReasLib.RingTheory.Etale.Weakly.IndEtale
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of ind-etale ring maps

This file owns the canonical map from an ind-etale fiber to the product of its
branch residue fields.  The Noetherian source-facing results are accompanied by
versions that only assume the selected fiber is Noetherian.

@stack 0AH1
-/

@[expose] public section

universe u v

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The canonical map from `p.Fiber B` to the product of the residue fields at
the primes of `B` lying over `p`. -/
@[stacks 0AH1 "canonical map from an ind-etale fiber to branch residue fields"]
noncomputable def fiberToPiResidueField (p : Ideal A) [p.IsPrime]
    (B : Type v) [CommRing B] [Algebra A B] :
    p.Fiber B →+* ∀ q : p.primesOver B, q.1.ResidueField :=
  let φ : ∀ q : p.primesOver B, p.Fiber B →+* q.1.ResidueField :=
    fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p q.1 (Algebra.ofId _ _) (q.1.over_def p))
        (IsScalarTower.toAlgHom _ _ _)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
  RingHom.pi φ

end Ideal

namespace RingHom.IndEtale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- If one fiber of an ind-etale map is Noetherian, only finitely many primes
of the target lie over its base prime. -/
@[stacks 0AH1 "finite branches of a Noetherian ind-etale fiber"]
theorem primesOver_finite_of_isNoetherianFiber
    (h : (algebraMap A B).IndEtale) (p : PrimeSpectrum A)
    [IsNoetherianRing (p.asIdeal.Fiber B)] :
    _root_.Finite (p.asIdeal.primesOver B) := sorry

/-- For a Noetherian fiber of an ind-etale map, its canonical map to the
product of the branch residue fields is bijective. -/
@[stacks 0AH1 "Noetherian ind-etale fiber decomposition"]
theorem fiberToPiResidueField_bijective_of_isNoetherianFiber
    (h : (algebraMap A B).IndEtale) (p : PrimeSpectrum A)
    [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Function.Bijective (p.asIdeal.fiberToPiResidueField B) := sorry

/-- Lemma 15.45.12 (1) (0AH1): if `B` is a Noetherian ind-etale
`A`-algebra, then only finitely many primes of `B` lie over `p`. -/
@[stacks 0AH1 "Lemma 15.45.12 (1): finite primes over the base prime"]
theorem primesOver_finite
    (h : (algebraMap A B).IndEtale) (p : PrimeSpectrum A)
    [IsNoetherianRing B] : _root_.Finite (p.asIdeal.primesOver B) := sorry

/-- Lemma 15.45.12 (2) (0AH1): for a Noetherian ind-etale algebra,
the canonical map from the fiber to the product of its branch residue fields
is bijective. -/
@[stacks 0AH1 "Lemma 15.45.12 (2): fiber product decomposition"]
theorem fiberToPiResidueField_bijective
    (h : (algebraMap A B).IndEtale) (p : PrimeSpectrum A)
    [IsNoetherianRing B] :
    Function.Bijective (p.asIdeal.fiberToPiResidueField B) := sorry

/-- Lemma 15.45.12 (3) (0AH1): residue fields along an ind-etale
map are separable algebraic extensions. -/
@[stacks 0AH1 "Lemma 15.45.12 (3): separable algebraic residue fields"]
theorem residueField_isAlgebraic_and_separable
    (h : (algebraMap A B).IndEtale) (p : PrimeSpectrum A)
    (q : p.asIdeal.primesOver B) :
    -- Local instance justification: lies-over canonically determines this residue-field algebra
    -- structure; it is confined to the conclusion to avoid a competing global instance.
    letI : Algebra p.asIdeal.ResidueField q.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p.asIdeal q.1
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := sorry

end RingHom.IndEtale
