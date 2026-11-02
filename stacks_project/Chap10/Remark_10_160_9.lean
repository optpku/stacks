/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.KrullDimension.MvPowerSeries
public import stacks_project.Chap10.Remark_10_160_9.RegularSingleton
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohen structure and complete local rings

@stack 032C

The construction of a Cohen presentation belongs to the proof stage. This file records its two
source conclusions together with the finite-variable power-series facts used by later chapters.
-/

@[expose] public section

open IsLocalRing

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Formal power series in finitely many variables over a Noetherian complete local ring form a
complete local ring. -/
instance mvPowerSeries_fin_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] (d : ℕ) :
    IsCompleteLocalRing (MvPowerSeries (Fin d) R) := sorry

/-- Formal power series in finitely many variables over a regular local ring form a regular local
ring. -/
instance mvPowerSeries_fin_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin d) R) := sorry

/-- The Krull dimension of the `d`-variable formal power series ring over a field is `d`. -/
theorem ringKrullDim_mvPowerSeries_fin_field (k : Type u) [Field k] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) k) = d :=
  MvPowerSeries.ringKrullDim_fin_field k d

/-- In particular, power series in `d` variables over a Cohen ring have dimension `d + 1`:
the dimension formula holds over any discrete valuation ring. -/
@[stacks 032C]
theorem ringKrullDim_mvPowerSeries_fin_dvr (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (d : ℕ) :
    ringKrullDim (MvPowerSeries (Fin d) R) = (d : WithBot ℕ∞) + 1 :=
  MvPowerSeries.ringKrullDim_fin_dvr R d

/-- Chap10 Remark 10 160 9 (1): every Noetherian complete local ring is a quotient of a regular
local ring. -/
@[stacks 032C]
theorem exists_regularLocalRing_quotient_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (I : Ideal S),
      Nonempty ((S ⧸ I) ≃+* R) := sorry

/-- Chap10 Remark 10 160 9 (2): a Noetherian complete local ring is universally catenary. -/
@[stacks 032C]
theorem universallyCatenaryRing_of_isCompleteLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsCompleteLocalRing R] :
    UniversallyCatenaryRing.{u, u} R := sorry

#check @mvPowerSeries_fin_isCompleteLocalRing
#check @mvPowerSeries_fin_isRegularLocalRing
#check @ringKrullDim_mvPowerSeries_fin_field
#check @ringKrullDim_mvPowerSeries_fin_dvr
#check @MvPowerSeries.ringKrullDim_fin_field
#check @exists_regularLocalRing_quotient_of_isCompleteLocalRing
#check @universallyCatenaryRing_of_isCompleteLocalRing
