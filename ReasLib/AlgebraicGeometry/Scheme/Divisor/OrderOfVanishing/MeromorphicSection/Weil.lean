/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing.MeromorphicSection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weil divisors of meromorphic sections

A regular meromorphic section of an invertible module determines a Weil divisor from its orders
along prime divisors, and hence a well-defined class in the Weil divisor class group.
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
variable [PrimeDivisorDiscreteValuationRings X]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/-- The coefficient of the Weil divisor of a meromorphic section at a prime divisor. -/
@[stacks 0BE6 "coefficient"]
def meromorphicSectionWeilDivisorCoeff
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) : ℤ :=
  primeDivisorOrderOfVanishing s Z (data Z)

/-- The coefficient is the order of vanishing supplied by the local presentation. -/
theorem meromorphicSectionWeilDivisorCoeff_def
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) :
    meromorphicSectionWeilDivisorCoeff ℒ s data Z =
      primeDivisorOrderOfVanishing s Z (data Z) :=
  rfl

/-- The nonzero coefficients of the Weil divisor of a meromorphic section are locally finite. -/
theorem locallyFinite_meromorphicSectionWeilDivisorCoeff_ne_zero
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if meromorphicSectionWeilDivisorCoeff ℒ s data Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- Two meromorphic-section coefficient functions differ by the principal-divisor coefficients of
a function-field unit. -/
@[stacks 0BE6 "well-definedness"]
theorem exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (data' : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s' Z) :
    ∃ f : X.functionFieldˣ,
      ∀ Z : PrimeDivisor X,
        meromorphicSectionWeilDivisorCoeff ℒ s data Z =
          meromorphicSectionWeilDivisorCoeff ℒ s' data' Z +
            principalWeilDivisorCoeff X (primeDivisorDiscreteValuationRing X) f Z :=
  sorry

variable (X)

/-- The Weil divisor associated to a meromorphic section. -/
@[stacks 0BE6 "Weil divisor"]
noncomputable def meromorphicSectionWeilDivisor
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) : Div(X) :=
  WeilDivisor.ofCoeff X
    (fun Z ↦ meromorphicSectionWeilDivisorCoeff ℒ s data Z)
    (locallyFinite_meromorphicSectionWeilDivisorCoeff_ne_zero ℒ s data)

@[simp] theorem meromorphicSectionWeilDivisor_coeff
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) :
    (meromorphicSectionWeilDivisor X ℒ s data).coeff Z =
      meromorphicSectionWeilDivisorCoeff ℒ s data Z :=
  rfl

/-- The Weil divisor class associated to a meromorphic section. -/
@[stacks 0BE6 "divisor class"]
noncomputable def meromorphicSectionWeilDivisorClass
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) : Cl(X) :=
  weilDivisorClassGroupMk X <| meromorphicSectionWeilDivisor X ℒ s data

@[simp] theorem meromorphicSectionWeilDivisorClass_def
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    meromorphicSectionWeilDivisorClass X ℒ s data =
      weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s data) :=
  rfl

/-- The divisor class is independent of the meromorphic section and local presentations used to
compute it. -/
theorem meromorphicSectionWeilDivisorClass_eq
    [MonoidalCategory ModX]
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (data' : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s' Z) :
    meromorphicSectionWeilDivisorClass X ℒ s data =
      meromorphicSectionWeilDivisorClass X ℒ s' data' := by
  rcases exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
      (X := X) ℒ s s' data data' with ⟨f, hf⟩
  have hdiv :
      meromorphicSectionWeilDivisor X ℒ s data =
        meromorphicSectionWeilDivisor X ℒ s' data' + principalWeilDivisor X f := by
    ext Z
    simpa using hf Z
  have hprincipal :
      weilDivisorClassGroupMk X (principalWeilDivisor X f) = 0 := by
    exact (QuotientAddGroup.eq_zero_iff (principalWeilDivisor X f)).2
      (principalWeilDivisor_mem_principalWeilDivisors X f)
  calc
    meromorphicSectionWeilDivisorClass X ℒ s data
        = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s data) := rfl
    _ = weilDivisorClassGroupMk X
          (meromorphicSectionWeilDivisor X ℒ s' data' + principalWeilDivisor X f) := by
      rw [hdiv]
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' data') +
          weilDivisorClassGroupMk X (principalWeilDivisor X f) := by
      simpa using
        (weilDivisorClassGroupMk X).map_add
          (meromorphicSectionWeilDivisor X ℒ s' data') (principalWeilDivisor X f)
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' data') := by
      rw [hprincipal, add_zero]
    _ = meromorphicSectionWeilDivisorClass X ℒ s' data' := rfl

end AlgebraicGeometry.Scheme
