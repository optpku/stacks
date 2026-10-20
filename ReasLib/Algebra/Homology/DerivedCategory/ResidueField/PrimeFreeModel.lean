/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime residue-field homology and free models

A perfect derived module has finite-support homology after extension to a prime residue field, and
its prime-local minimal free model descends to a suitable away localization.

@stack 0BCD
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (instance diamond): use the standard derived-category model only
-- for the prime-local free-model construction.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.PrimeResidueField

variable {R : Type u} [CommRing R]

/-- The degree-`i` homology of `K ⊗[R]^L κ(p)`. -/
@[stacks 0BCD "Prime residue-field homology"]
abbrev homology (p : PrimeSpectrum R) (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    ModuleCat p.asIdeal.ResidueField :=
  (DerivedCategory.homologyFunctor (ModuleCat p.asIdeal.ResidueField) i).obj
    (K ⊗[R]^L[p.asIdeal.ResidueField])

/-- The finite-free object property over the away localization `R_f`. -/
@[stacks 0BCD "Away finite free module property"]
abbrev awayFiniteFree (f : R) : ObjectProperty (ModuleCat (Localization.Away f)) :=
  fun M => Module.Free (Localization.Away f) M ∧ Module.Finite (Localization.Away f) M

/-- Bounded-above finite-free cochain complexes over `R_f`. -/
@[stacks 0BCD "Away bounded-above finite free complexes"]
abbrev AwayBoundedFiniteFree (f : R) :=
  CochainComplex.Minus.TermsIn (awayFiniteFree f)

/-- Lemma 15.76.7 (0BCD), finiteness clause: the prime residue-field homology of a perfect
derived module is finite-dimensional and has finite support. -/
@[stacks 0BCD "Prime residue-field homology has finite support"]
theorem finiteDimensional_and_finiteSupport
    (p : PrimeSpectrum R) (K : DerivedCategory (ModuleCat R)) (hK : K.IsPerfect) :
    (∀ i : ℤ, FiniteDimensional p.asIdeal.ResidueField (homology p K i)) ∧
      Set.Finite {i : ℤ | ¬ IsZero (homology p K i)} := sorry

/-- Lemma 15.76.7 (0BCD), model clause: after inverting one element outside `p`, the prescribed
prime residue-field dimensions are realized by a bounded finite-free model. -/
@[stacks 0BCD "Existence of an away minimal free model"]
theorem existsAwayFreeModel
    (p : PrimeSpectrum R) (K : DerivedCategory (ModuleCat R)) (hK : K.IsPerfect)
    (d : ℤ → ℕ)
    (hd : ∀ i : ℤ, Module.finrank p.asIdeal.ResidueField (homology p K i) = d i) :
    ∃ f : R, ∃ hf : f ∉ p.asIdeal, ∃ a : ℤ, ∃ P : AwayBoundedFiniteFree f,
      (P : CochainComplex (ModuleCat (Localization.Away f)) ℤ).IsStrictlyGE a ∧
        (∀ i : ℤ,
          Nonempty
            (((P : CochainComplex (ModuleCat (Localization.Away f)) ℤ).X i) ≃ₗ[
              Localization.Away f] (Fin (d i) → Localization.Away f))) ∧
        Nonempty
          ((K ⊗[R]^L[Localization.Away f]) ≅
            DerivedCategory.Q.obj
              (P : CochainComplex (ModuleCat (Localization.Away f)) ℤ)) := sorry

end CategoryTheory.DerivedCategory.PrimeResidueField
