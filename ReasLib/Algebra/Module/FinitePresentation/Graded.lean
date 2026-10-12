/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Data.PNat.Notation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.FinitePresentation.PrimeLocalization

/-!
# Finite presentation for flat graded modules

This leaf owns the weighted-polynomial local criterion and the two global graded flatness
criteria for finite presentation.

@stack 053C
@stack 053D
-/

@[expose] public section

universe u v w

/-- Local instance justification (defeq pin): natural algebra degrees act on integer module
degrees through the standard inclusion `ℕ → ℤ`. -/
local instance : AddAction ℕ ℤ := AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

namespace Module.FinitePresentation

/-- Lemma 15.25.3: a finite graded module over a positively weighted polynomial ring over a
local ring is finitely presented when it is flat over the base ring. -/
@[stacks 053C "Lemma 15.25.3"]
theorem ofWeightedGradedFlat
    {R : Type u} [CommRing R] [IsLocalRing R]
    {σ : Type*} [Finite σ] (w : σ → ℕ+)
    {M : Type v} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Finite (MvPolynomial σ R) M] [Module.Flat R M] :
    Module.FinitePresentation (MvPolynomial σ R) M := sorry

/-- Lemma 15.25.4 (2): a finite graded module over a finite-type nonnegatively graded algebra
whose degree-zero part is finite over the base is finitely presented when it is flat over the
base and finitely many prime localizations detect equality. -/
@[stacks 053D "Lemma 15.25.4 (2)"]
theorem ofGradedFlat
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
    [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)]
    (hdetect : PrimeLocalization.DetectsEquality R)
    {M : Type w} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Flat R M] [Module.Finite S M] :
    Module.FinitePresentation S M := sorry

end Module.FinitePresentation

namespace Algebra.FinitePresentation

/-- Lemma 15.25.4 (1): a flat finite-type nonnegatively graded algebra whose degree-zero part is
finite over the base is finitely presented when finitely many prime localizations detect
equality. -/
@[stacks 053D "Lemma 15.25.4 (1)"]
theorem ofGradedFlat
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
    [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)] [Module.Flat R S]
    (hdetect : PrimeLocalization.DetectsEquality R) :
    Algebra.FinitePresentation R S := sorry

end Algebra.FinitePresentation
