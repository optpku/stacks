/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Completion.CohenRing
public import ReasLib.RingTheory.RegularLocalRing.Parameters
import Mathlib.Tactic.CrossRefAttribute

/-!
# Power Series Coordinates from Regular Parameters

Regular systems of parameters define coordinate changes in finite-variable power series rings.
Over a field this is ordinary substitution.  Over a Cohen ring, evaluation uses the
maximal-ideal-adic topology on the coefficient ring.

@stack 07NM
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

universe u

namespace MvPowerSeries

section Field

variable {K : Type u} [Field K] {n : ℕ}

local notation "P" => MvPowerSeries (Fin n) K

/-- A series in the maximal ideal of a power series ring over a field has zero constant
coefficient. -/
theorem constantCoeff_eq_zero_of_mem_maximalIdeal (y : maximalIdeal P) :
    constantCoeff (y : P) = 0 := sorry

/-- The canonical coordinate substitution associated to a family in the maximal ideal of a
finite-variable power series ring over a field. -/
@[stacks 07NM "substitution by a family in the maximal ideal"]
noncomputable def regularParameterSubst (y : Fin n → maximalIdeal P) : P →ₐ[K] P :=
  MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦
      constantCoeff_eq_zero_of_mem_maximalIdeal (y i))

/-- The regular-parameter substitution sends each coordinate variable to the corresponding
chosen parameter. -/
@[simp]
theorem regularParameterSubst_X (y : Fin n → maximalIdeal P) (i : Fin n) :
    regularParameterSubst y (X i) = y i := sorry

/-- Lemma 15.39.2 (1) (Stacks `07NM`): substitution by a regular system of parameters of
`MvPowerSeries (Fin n) K` is bijective. -/
@[stacks 07NM "part 1"]
theorem regularParameterSubst_bijective (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters y) : Function.Bijective (regularParameterSubst y) := sorry

/-- Lemma 15.39.2 (2) (Stacks `07NM`): if `z` is part of a regular system of parameters of
`MvPowerSeries (Fin n) K`, then the quotient by its parameter ideal is a power series ring in
`n - r` variables, with a complementary parameter family giving the coordinates. -/
@[stacks 07NM "part 2"]
theorem exists_quotientAlgEquiv_of_isPartOfRegularSystemOfParameters
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters n z) :
    ∃ y : Fin (n - r) → maximalIdeal P,
      ∃ e : (P ⧸ parameterIdeal z) ≃ₐ[K] MvPowerSeries (Fin (n - r)) K,
        ∀ i, e (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := sorry

end Field

section CohenRing

variable {Λ : Type u} [CommRing Λ] [IsCohenRing Λ] {n : ℕ}

local notation "P" => MvPowerSeries (Fin n) Λ

/-- The image in `MvPowerSeries (Fin n) Λ` of the residue characteristic of a Cohen ring lies in
the maximal ideal. -/
theorem cohenResidueCharacteristic_mem_maximalIdeal :
    algebraMap Λ P (ringChar (ResidueField Λ)) ∈ maximalIdeal P := sorry

/-- The residue characteristic, regarded as an element of the maximal ideal of a power series
ring over a Cohen ring. -/
@[stacks 07NM "residue characteristic as a power-series parameter"]
def cohenResidueCharacteristicParameter : maximalIdeal P :=
  ⟨algebraMap Λ P (ringChar (ResidueField Λ)),
    cohenResidueCharacteristic_mem_maximalIdeal⟩

/-- Local instance justification (defeq pin): use the maximal-ideal-adic topology throughout the
Cohen-ring power series evaluation construction. -/
local instance cohenAdicTopology : TopologicalSpace Λ := Ideal.adicTopology (maximalIdeal Λ)

/-- Local instance justification (defeq pin): use the right uniformity associated to the chosen
maximal-ideal-adic additive topology. -/
local instance cohenAdicUniformSpace : UniformSpace Λ :=
  IsTopologicalAddGroup.rightUniformSpace Λ

/-- Local instance justification (proof-local temporary data): record additive compatibility of
the selected adic uniformity only within this construction. -/
local instance cohenAdicIsUniformAddGroup : IsUniformAddGroup Λ := sorry

/-- Local instance justification (proof-local temporary data): record the ring-topology law for
the selected adic topology only within this construction. -/
local instance cohenAdicIsTopologicalRing : IsTopologicalRing Λ := sorry

/-- Local instance justification (defeq pin): take the maximal ideal as the distinguished ideal
for the selected adic topology. -/
local instance cohenAdicWithIdeal : WithIdeal Λ := ⟨maximalIdeal Λ⟩

/-- Local instance justification (proof-local temporary data): expose completeness for the
selected adic uniformity only while constructing evaluation. -/
local instance cohenAdicCompleteSpace : CompleteSpace Λ := sorry

/-- Local instance justification (proof-local temporary data): expose separation for the selected
adic topology only while constructing evaluation. -/
local instance cohenAdicT2Space : T2Space Λ := sorry

/-- A finite family in the maximal ideal of a power series ring over a Cohen ring admits
convergent power series evaluation. -/
theorem hasEval_of_mem_maximalIdeal {σ : Type*} [Finite σ]
    (y : σ → maximalIdeal P) : HasEval (fun i ↦ (y i : P)) := sorry

/-- The canonical continuous evaluation map associated to a finite family in the maximal ideal
of a power series ring over a Cohen ring. -/
@[stacks 07NM "continuous evaluation at Cohen-ring parameters"]
noncomputable def cohenParameterEval (y : Fin n → maximalIdeal P) :
    MvPowerSeries (Fin n) Λ →ₐ[Λ] P :=
  MvPowerSeries.aeval (hasEval_of_mem_maximalIdeal y)

/-- The Cohen-ring parameter evaluation sends each coordinate variable to the corresponding
chosen parameter. -/
@[simp]
theorem cohenParameterEval_X (y : Fin n → maximalIdeal P) (i : Fin n) :
    cohenParameterEval y (X i) = y i := sorry

/-- Lemma 15.39.2 (3) (Stacks `07NM`): if the residue characteristic followed by `y` is a
regular system of parameters, then continuous evaluation at `y` is bijective. -/
@[stacks 07NM "part 3"]
theorem cohenParameterEval_bijective (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.cons cohenResidueCharacteristicParameter y)) :
    Function.Bijective (cohenParameterEval y) := sorry

/-- Lemma 15.39.2 (4), inequality clause (Stacks `07NM`): if the residue characteristic followed
by an `r`-term family is part of a regular system of parameters of length `n + 1`, then `r ≤ n`. -/
@[stacks 07NM "part 4 length"]
theorem cohenPartialParameters_length_le {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1)
      (Fin.cons cohenResidueCharacteristicParameter z)) :
    r ≤ n := sorry

/-- Lemma 15.39.2 (4) (Stacks `07NM`): if the residue characteristic followed by `z` is part of
a regular system of parameters, then quotienting by the parameter ideal of `z` leaves a power
series ring in `n - r` variables over the same Cohen ring. -/
@[stacks 07NM "part 4"]
theorem exists_cohenQuotientAlgEquiv_of_isPartOfRegularSystemOfParameters
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1)
      (Fin.cons cohenResidueCharacteristicParameter z)) :
    ∃ y : Fin (n - r) → maximalIdeal P,
      ∃ e : (P ⧸ parameterIdeal z) ≃ₐ[Λ] MvPowerSeries (Fin (n - r)) Λ,
        ∀ i, e (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := sorry

end CohenRing

end MvPowerSeries
