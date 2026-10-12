/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap91.Lemma_91_2_1_Obstruction

/-!
# Finite-dimensionality of Inf and T for finite type ring deformations

In Lemma 93.8.3, `Inf(Def_P)` identifies with `Derivation k P P` and `T Def_P`
identifies with `extOneNaiveCotangent k P P`. For a finite type `k`-algebra `P`,
the former is finite-dimensional iff `dim(P) = 0`, and the latter is
finite-dimensional if `Spec(P) ⟶ Spec(k)` is smooth except at finitely many points.
-/

@[expose] public section

universe u

open Algebra RingHom.SquareZeroExtension

variable (k : Type u) [Field k]

/-- Lemma 93.8.5 (1)
In Lemma 93.8.3, if `P` is a finite type `k`-algebra, then `Inf(Def_P)` is
finite-dimensional if and only if `dim(P) = 0`. Here `Inf(Def_P)` is identified
with `Derivation k P P` via `infAutOfDerivation_bijective`, and `dim(P) = 0` is
`Ring.KrullDimLE 0 P`. -/
@[stacks 0DY4]
theorem finiteDimensional_derivations_iff (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] :
    FiniteDimensional k (Derivation k P P) ↔ Ring.KrullDimLE 0 P := sorry

/-- Lemma 93.8.5 (2)
In Lemma 93.8.3, if `P` is a finite type `k`-algebra, then `T Def_P` is
finite-dimensional whenever `Spec(P) ⟶ Spec(k)` is smooth except at finitely
many points. Here `T Def_P` is identified with `extOneNaiveCotangent k P P` via
`ofExtClass_bijective`, and the finite nonsmooth locus is
`(smoothLocus k P)ᶜ.Finite`. -/
@[stacks 0DY4]
theorem finiteDimensional_extOne_of_finite_nonsmooth (P : Type u) [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (h : (smoothLocus k P)ᶜ.Finite) :
    FiniteDimensional k (extOneNaiveCotangent k P P) := sorry

/-- Finite-dimensionality of `Derivation k P P` is equivalent to `ringKrullDim P ≤ 0`. -/
theorem finiteDimensional_derivations_iff_ringKrullDim (P : Type u) [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] :
    FiniteDimensional k (Derivation k P P) ↔ ringKrullDim P ≤ 0 := sorry
