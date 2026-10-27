/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth.Equiv
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local Bridges for Cohen-Macaulay Modules

Transport under linear equivalence and the comparison between local and primewise
Cohen-Macaulayness.

@stack 0AAG
@stack 00RG
-/

universe u v w

open scoped ENat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module.CohenMacaulay

/-- Cohen-Macaulayness is preserved by an `R`-linear equivalence over a Noetherian local ring. -/
theorem of_linearEquiv [IsLocalRing R] {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [h : Module.CohenMacaulay R M] :
    Module.CohenMacaulay R N := by
  letI : Module.Finite R N := Module.Finite.equiv e
  letI : Nontrivial M := (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by
    rw [h.supportDim_eq_moduleDepth]
    simp)
  letI : Nontrivial N := e.symm.toEquiv.nontrivial
  have hM := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hN := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R N))).symm
  have hlengths : Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal R) M =
      Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal R) N := by
    ext d
    simp only [Ideal.regularSequenceLengths, Set.mem_setOf_eq, e.isRegular_congr]
  have hdepth : moduleDepth R M = moduleDepth R N := by
    simp only [moduleDepth, Ideal.depth, if_neg hM, if_neg hN, hlengths]
  refine { supportDim_eq_moduleDepth := ?_ }
  calc
    Module.supportDim R N = Module.supportDim R M := (Module.supportDim_eq_of_equiv e).symm
    _ = .some (moduleDepth R M) := h.supportDim_eq_moduleDepth
    _ = .some (moduleDepth R N) := congrArg WithBot.some hdepth

/-- A finite module with zero support dimension over a Noetherian local ring is
Cohen-Macaulay. -/
theorem of_supportDim_eq_zero [IsLocalRing R] [Module.Finite R M]
    (hdim : Module.supportDim R M = 0) :
    Module.CohenMacaulay R M := by
  letI : Nontrivial M := (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by
    rw [hdim]
    simp)
  have hM := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hdepth : moduleDepth R M = 0 := by
    simp only [moduleDepth, Ideal.depth, if_neg hM]
    apply le_antisymm
    · change sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal R) M) ≤ 0
      refine sSup_le ?_
      rintro d ⟨rs, hrs, _, rfl⟩
      letI := hrs.quot_ofList_smul_nontrivial (⊤ : Submodule R M)
      have hnonneg : 0 ≤ Module.supportDim R
          (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) := by
        letI : Nonempty (Module.support R
            (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
          Module.nonempty_support_of_nontrivial.to_subtype
        exact Order.krullDim_nonneg
      have hlen : (rs.length : WithBot ℕ∞) ≤ 0 := by
        calc
          (rs.length : WithBot ℕ∞) = 0 + rs.length := (zero_add _).symm
          _ ≤ Module.supportDim R (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) +
              rs.length := add_le_add hnonneg le_rfl
          _ = 0 := (Module.supportDim_add_length_eq_supportDim_of_isRegular rs hrs).trans hdim
      exact WithBot.coe_le_coe.mp hlen
    · change 0 ≤ sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal R) M)
      exact zero_le
  exact { supportDim_eq_moduleDepth := by simpa [hdepth] using hdim }

/-- A Noetherian local ring of Krull dimension zero is Cohen--Macaulay as its
self-module.  The general finite-module construction is
`Module.CohenMacaulay.of_supportDim_eq_zero`; this theorem supplies the
self-module dimension bridge used by local algebra applications. -/
@[stacks 00RG "zero-dimensional local rings are Cohen--Macaulay"]
theorem self_of_ringKrullDim_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 0) :
    Module.CohenMacaulay R R := by
  apply of_supportDim_eq_zero
  exact (Module.supportDim_self_eq_ringKrullDim R).trans hdim

/-- A Noetherian local ring with Krull dimension at most zero is
Cohen--Macaulay as its self-module.  This class-oriented form is convenient
when the dimension bound is already available to typeclass search. -/
@[stacks 00RG "zero-dimensional local rings are Cohen--Macaulay"]
theorem self_of_krullDimLE_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 0 R] :
    Module.CohenMacaulay R R := by
  apply self_of_ringKrullDim_eq_zero
  exact (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := R)).mp inferInstance

/-- Localizing a Cohen--Macaulay module at a prime in its support remains
Cohen--Macaulay. -/
@[stacks 0AAG]
theorem localizedModule_atPrime [IsLocalRing R] [Module.CohenMacaulay R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := sorry

/-- Localizing a Cohen--Macaulay module at any prime either preserves
Cohen--Macaulayness or produces the zero module. -/
@[stacks 0AAG "including the zero localization"]
theorem localizedModule_atPrime_or_subsingleton
    [IsLocalRing R] [Module.CohenMacaulay R M] (p : PrimeSpectrum R) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) ∨
      Subsingleton (LocalizedModule.AtPrime p.asIdeal M) := by
  by_cases hp : p ∈ Module.support R M
  · exact Or.inl (localizedModule_atPrime p hp)
  · exact Or.inr (Module.notMem_support_iff.mp hp)

end Module.CohenMacaulay

namespace Module.LocallyCohenMacaulay

attribute [local instance] RingHomInvPair.of_ringEquiv

omit [IsNoetherianRing R] in
private theorem supportDim_eq_of_ringEquiv
    {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
    [Module.Finite R M] [Module.Finite S N]
    (f : R ≃+* S) (e : M ≃ₛₗ[(f : R →+* S)] N) :
    Module.supportDim R M = Module.supportDim S N := by
  have hann : (Module.annihilator S N).comap (f : R →+* S) = Module.annihilator R M := by
    ext r
    constructor
    · intro hr
      apply Module.mem_annihilator.mpr
      intro m
      apply e.injective
      calc
        e (r • m) = f r • e m := e.map_smul' r m
        _ = 0 := Module.mem_annihilator.mp hr (e m)
        _ = e 0 := (map_zero e).symm
    · intro hr
      apply Module.mem_annihilator.mpr
      intro n
      obtain ⟨m, rfl⟩ := e.surjective n
      calc
        f r • e m = e (r • m) := (e.map_smul' r m).symm
        _ = e 0 := congrArg e (Module.mem_annihilator.mp hr m)
        _ = 0 := map_zero e
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact (Ideal.quotientEquiv (Module.annihilator R M) (Module.annihilator S N) f
    (by rw [← hann, Ideal.map_comap_of_surjective (f : R →+* S) f.surjective])).ringKrullDim

omit [IsNoetherianRing R] in
private theorem moduleDepth_eq_of_ringEquiv
    [IsLocalRing R] {S : Type*} [CommRing S] [IsLocalRing S]
    {N : Type*} [AddCommGroup N] [Module S N]
    [Module.Finite R M] [Module.Finite S N] [Nontrivial M] [Nontrivial N]
    (f : R ≃+* S) (e : M ≃ₛₗ[(f : R →+* S)] N) :
    moduleDepth R M = moduleDepth S N := by
  have hM := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hN := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator S N))).symm
  have hlengths : Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal R) M =
      Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal S) N := by
    ext d
    constructor
    · rintro ⟨rs, hreg, hI, hd⟩
      refine ⟨rs.map (f : R →+* S), (e.isRegular_congr' rs).mp hreg, ?_, by simpa using hd⟩
      rw [← Ideal.map_ofList, ← IsLocalRing.map_ringEquiv_maximalIdeal f]
      exact Ideal.map_mono hI
    · rintro ⟨rs, hreg, hI, hd⟩
      refine ⟨rs.map (f.symm : S →+* R), (e.symm.isRegular_congr' rs).mp hreg, ?_,
        by simpa using hd⟩
      rw [← Ideal.map_ofList, ← IsLocalRing.map_ringEquiv_maximalIdeal f.symm]
      exact Ideal.map_mono hI
  simp only [moduleDepth, Ideal.depth, if_neg hM, if_neg hN, hlengths]

/-- A locally Cohen-Macaulay module has full support. -/
theorem support_eq_univ (h : Module.LocallyCohenMacaulay R M) :
    Module.support R M = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hp := (h.localizedModule_cohenMacaulay p).supportDim_eq_moduleDepth
  apply Module.mem_support_iff.mpr
  apply (Module.supportDim_ne_bot_iff_nontrivial (Localization.AtPrime p.asIdeal)
    (LocalizedModule.AtPrime p.asIdeal M)).mp
  rw [hp]
  simp

/-- Local Cohen-Macaulayness is preserved by an `R`-linear equivalence. -/
theorem of_linearEquiv {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [h : Module.LocallyCohenMacaulay R M] :
    Module.LocallyCohenMacaulay R N := by
  letI : Module.Finite R N := Module.Finite.equiv e
  refine { localizedModule_cohenMacaulay := ?_ }
  intro p
  letI := h.localizedModule_cohenMacaulay p
  exact Module.CohenMacaulay.of_linearEquiv
    (IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      (Localization.AtPrime p.asIdeal) e)

/-- Over a Noetherian local ring, a locally Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay [IsLocalRing R] (h : Module.LocallyCohenMacaulay R M) :
    Module.CohenMacaulay R M := by
  letI := h
  let p := IsLocalRing.closedPoint R
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  have hunits : p.asIdeal.primeCompl ≤ IsUnit.submonoid R := by
    intro r hr
    exact IsLocalRing.notMem_maximalIdeal.mp hr
  letI : IsLocalization p.asIdeal.primeCompl R := IsLocalization.of_le_isUnit hunits
  letI : IsLocalizedModule p.asIdeal.primeCompl (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id p.asIdeal.primeCompl M R
  let f : R ≃+* S := (IsLocalization.atUnits R p.asIdeal.primeCompl hunits).toRingEquiv
  let eR : M ≃ₗ[R] N := (IsLocalizedModule.iso p.asIdeal.primeCompl
    (LinearMap.id : M →ₗ[R] M)).symm
  let e : M ≃ₛₗ[(f : R →+* S)] N :=
    { eR.toAddEquiv with
      map_smul' r m := by
        change eR (r • m) = algebraMap R S r • eR m
        rw [eR.map_smul, algebraMap_smul] }
  letI hN : Module.CohenMacaulay S N := h.localizedModule_cohenMacaulay p
  letI : Nontrivial N := (Module.supportDim_ne_bot_iff_nontrivial S N).mp (by
    rw [hN.supportDim_eq_moduleDepth]
    simp)
  letI : Nontrivial M := e.toEquiv.nontrivial
  refine { supportDim_eq_moduleDepth := ?_ }
  calc
    Module.supportDim R M = Module.supportDim S N := supportDim_eq_of_ringEquiv f e
    _ = .some (moduleDepth S N) := hN.supportDim_eq_moduleDepth
    _ = .some (moduleDepth R M) := congrArg WithBot.some (moduleDepth_eq_of_ringEquiv f e).symm

end Module.LocallyCohenMacaulay

namespace Module

/-- Over a Noetherian local ring, local Cohen-Macaulayness supplies a Cohen-Macaulay instance. -/
instance cohenMacaulay_of_locallyCohenMacaulay [IsLocalRing R]
    [h : Module.LocallyCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  h.toCohenMacaulay

/-- Over a Noetherian local ring, a Cohen-Macaulay module with full support is locally
Cohen-Macaulay. -/
theorem locallyCohenMacaulay_of_cohenMacaulay [IsLocalRing R] [Module.CohenMacaulay R M]
    (hsupp : Module.support R M = Set.univ) :
    Module.LocallyCohenMacaulay R M := by
  refine { localizedModule_cohenMacaulay := ?_ }
  intro p
  exact Module.CohenMacaulay.localizedModule_atPrime p (by simp [hsupp])

end Module

end
