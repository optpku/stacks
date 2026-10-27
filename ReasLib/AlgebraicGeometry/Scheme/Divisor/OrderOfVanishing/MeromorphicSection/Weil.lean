/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weil divisors of meromorphic sections

A nonzero meromorphic section of an invertible module determines a Weil divisor from its intrinsic
orders along prime divisors, and hence a well-defined class in the Weil divisor class group.
This file provides compatibility names for the intrinsic API in `Divisor.MeromorphicSection`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

/-- The intrinsic coefficient of the Weil divisor of a nonzero meromorphic section. -/
@[stacks 0BE6 "coefficient"]
abbrev meromorphicSectionWeilDivisorCoeff
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0)
    (Z : PrimeDivisor X) : ℤ :=
  nonzeroMeromorphicSectionWeilDivisorCoeff ℒ s hs Z

/-- The coefficient is the intrinsic order of vanishing of the nonzero section. -/
theorem meromorphicSectionWeilDivisorCoeff_def
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0)
    (Z : PrimeDivisor X) :
    meromorphicSectionWeilDivisorCoeff ℒ s hs Z =
      regularMeromorphicSectionOrderAlongPrimeDivisor s
        ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs) Z :=
  rfl

/-- The nonzero coefficients of the Weil divisor of a nonzero meromorphic section are locally
finite. -/
theorem locallyFinite_meromorphicSectionWeilDivisorCoeff_ne_zero
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if meromorphicSectionWeilDivisorCoeff ℒ s hs Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) :=
  locallyFinite_nonzeroMeromorphicSectionWeilDivisorCoeff_ne_zero ℒ s hs

/-- The intrinsic coefficient functions of two nonzero meromorphic sections of the same invertible
module differ by the orders of a function-field unit. -/
@[stacks 0BE6 "well-definedness"]
theorem exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) (hs' : s' ≠ 0) :
    ∃ f : X.functionFieldˣ,
      ∀ Z : PrimeDivisor X,
        meromorphicSectionWeilDivisorCoeff ℒ s hs Z =
          meromorphicSectionWeilDivisorCoeff ℒ s' hs' Z +
            X.ord (f : X.functionField) Z.genericPoint :=
  nonzeroMeromorphicSectionWeilDivisorCoeff.exists_functionFieldUnit_sub X ℒ s s' hs hs'

variable (X)

/-- The Weil divisor associated to a nonzero meromorphic section. -/
@[stacks 0BE6 "Weil divisor"]
noncomputable abbrev meromorphicSectionWeilDivisor
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) : Div(X) :=
  nonzeroMeromorphicSectionWeilDivisor X ℒ s hs

@[simp] theorem meromorphicSectionWeilDivisor_coeff
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0)
    (Z : PrimeDivisor X) :
    (meromorphicSectionWeilDivisor X ℒ s hs).coeff Z =
      meromorphicSectionWeilDivisorCoeff ℒ s hs Z :=
  rfl

/-- The Weil divisor class associated to a nonzero meromorphic section. -/
@[stacks 0BE6 "divisor class"]
noncomputable abbrev meromorphicSectionWeilDivisorClass
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) : Cl(X) :=
  nonzeroMeromorphicSectionWeilDivisorClass X ℒ s hs

@[simp] theorem meromorphicSectionWeilDivisorClass_def
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) :
    meromorphicSectionWeilDivisorClass X ℒ s hs =
      weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s hs) :=
  rfl

/-- The divisor class is independent of the nonzero meromorphic section used to compute it. -/
theorem meromorphicSectionWeilDivisorClass_eq
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) (hs' : s' ≠ 0) :
    meromorphicSectionWeilDivisorClass X ℒ s hs =
      meromorphicSectionWeilDivisorClass X ℒ s' hs' := by
  rcases exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
      (X := X) ℒ s s' hs hs' with ⟨f, hf⟩
  have hdiv :
      meromorphicSectionWeilDivisor X ℒ s hs =
        meromorphicSectionWeilDivisor X ℒ s' hs' + principalWeilDivisor X f := by
    ext Z
    simpa using hf Z
  have hprincipal :
      weilDivisorClassGroupMk X (principalWeilDivisor X f) = 0 := by
    exact (QuotientAddGroup.eq_zero_iff (principalWeilDivisor X f)).2
      (principalWeilDivisor_mem_principalWeilDivisors X f)
  calc
    meromorphicSectionWeilDivisorClass X ℒ s hs
        = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s hs) := rfl
    _ = weilDivisorClassGroupMk X
          (meromorphicSectionWeilDivisor X ℒ s' hs' + principalWeilDivisor X f) := by
      rw [hdiv]
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' hs') +
          weilDivisorClassGroupMk X (principalWeilDivisor X f) := by
      simpa using
        (weilDivisorClassGroupMk X).map_add
          (meromorphicSectionWeilDivisor X ℒ s' hs') (principalWeilDivisor X f)
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' hs') := by
      rw [hprincipal, add_zero]
    _ = meromorphicSectionWeilDivisorClass X ℒ s' hs' := rfl

end AlgebraicGeometry.Scheme
