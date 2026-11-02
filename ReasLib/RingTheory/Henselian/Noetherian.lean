/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Completion.Flat
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.FormallyEtale
public import ReasLib.RingTheory.Henselian.Henselization.Completion
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.Tensor
public import ReasLib.RingTheory.RingHom.IndEtale.Composition
public import ReasLib.RingTheory.Smooth.Adic.Completion

@[expose] public section

/-!
# Noetherianity and henselization

@stack 06LJ

Noetherianity is invariant under passing from a local ring to either a henselization or a strict
henselization. The individual ascent results live on their respective owners; this file records
their symmetric, source-independent interface.
-/

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace Henselization

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type v} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type w} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.3, equivalence (tag `06LJ`): Noetherianity of a local ring, of any
henselization, and of any strict henselization are equivalent. -/
@[stacks 06LJ "equivalence (1)-(3), Noetherianity is invariant under henselization"]
theorem noetherian_tfae :
    List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] := by
  have hh : IsNoetherianRing R ↔ IsNoetherianRing Rh := by
    constructor
    · intro h
      letI := h
      exact IsHenselizationOf.isNoetherianRing (R := R) (S := Rh)
    · intro h
      letI := h
      exact (isNoetherianRing_iff_ideal_fg R).2 fun I =>
        Ideal.FG.of_FG_map_of_faithfullyFlat (S := Rh)
          (Ideal.fg_of_isNoetherianRing _)
  have hs : IsNoetherianRing R ↔ IsNoetherianRing Rsh := by
    constructor
    · intro h
      letI := h
      exact IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
    · intro h
      letI := h
      exact (isNoetherianRing_iff_ideal_fg R).2 fun I =>
        Ideal.FG.of_FG_map_of_faithfullyFlat (S := Rsh)
          (Ideal.fg_of_isNoetherianRing _)
  apply List.tfae_of_forall (IsNoetherianRing R)
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact Iff.rfl
  rcases hp with rfl | hp
  · exact hh.symm
  rcases hp with rfl | hp
  · exact hs.symm
  · exact False.elim (by simpa using hp)

/-- Lemma 15.45.3 (a) (tag `06LJ`): the maximal-ideal completions of a henselization and a strict
henselization are Noetherian complete local rings. The local Noetherian instances in the result
are the source-derived consequences of part (1), kept local because their base rings are not
recoverable from the completion types. -/
@[stacks 06LJ "(a) completed henselizations are Noetherian complete local rings"]
theorem completions_noetherian_complete_local [IsNoetherianRing R] :
    let _ : IsNoetherianRing Rh :=
      IsHenselizationOf.isNoetherianRing (R := R) (S := Rh)
    let _ : IsNoetherianRing Rsh :=
      IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
    (IsNoetherianRing (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsLocalRing (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsAdicComplete
        (maximalIdeal (AdicCompletion (maximalIdeal Rh) Rh))
        (AdicCompletion (maximalIdeal Rh) Rh)) ∧
    (IsNoetherianRing (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      IsLocalRing (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      IsAdicComplete
        (maximalIdeal (AdicCompletion (maximalIdeal Rsh) Rsh))
        (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  letI := IsHenselizationOf.isNoetherianRing (R := R) (S := Rh)
  letI := IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- Lemma 15.45.3 (c) (tag `06LJ`): the structural maps from a henselization and a strict
henselization to their maximal-ideal completions are flat. -/
@[stacks 06LJ "(c) flatness of the completion maps"]
theorem completion_algebraMaps_flat [IsNoetherianRing R] :
    RingHom.Flat (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh)) ∧
      RingHom.Flat (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  letI := IsHenselizationOf.isNoetherianRing (R := R) (S := Rh)
  letI := IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
  exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance⟩

/-- Lemma 15.45.3 (d) (tag `06LJ`): the canonical map from the completion of the base to the
completion of a strict henselization is formally smooth for the target maximal-ideal topology. -/
@[stacks 06LJ "(d) formal smoothness of the strict completion map"]
theorem strictCompletionMap_formallySmooth [IsNoetherianRing R] :
    let _ : IsNoetherianRing Rsh :=
      IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
    (AdicCompletion.mapLocal (algebraMap R Rsh)).formally_smooth_for_adic
      (maximalIdeal (AdicCompletion (maximalIdeal Rsh) Rsh)) := by
  dsimp only
  letI := IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
  let hcont : (algebraMap R Rsh).AdicContinuous (maximalIdeal R)
      (maximalIdeal Rsh) :=
    ⟨1, by simpa using IsLocalRing.map_maximalIdeal_le (algebraMap R Rsh)⟩
  have hpos : 0 < hcont.exponent := by
    by_contra hn
    have hz : hcont.exponent = 0 := Nat.eq_zero_of_not_pos hn
    have htop := Classical.choose_spec hcont
    change Ideal.map (algebraMap R Rsh) ((maximalIdeal R) ^ hcont.exponent) ≤
      maximalIdeal Rsh at htop
    rw [hz, pow_zero, Ideal.one_eq_top, Ideal.map_top] at htop
    exact (maximalIdeal.isMaximal Rsh).ne_top (top_unique htop)
  have heq : hcont.completionMap = AdicCompletion.mapLocal (algebraMap R Rsh) := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change ((AdicCompletion.evalₐ (maximalIdeal Rsh) n).toRingHom.comp
      hcont.completionMap) x =
      ((AdicCompletion.evalₐ (maximalIdeal Rsh) n).toRingHom.comp
        (AdicCompletion.mapLocal (algebraMap R Rsh))) x
    rw [hcont.eval_completionMap, AdicCompletion.evalₐ_comp_mapLocal]
    induction x using AdicCompletion.induction_on (maximalIdeal R) R with
    | h x =>
      simp only [RingHom.AdicContinuous.quotientMap, AdicCompletion.localQuotientMap,
        RingHom.comp_apply, AlgHom.coe_toRingHom, AdicCompletion.evalₐ_mk,
        Ideal.quotientMap_mk]
      have hc' : Ideal.Quotient.mk ((maximalIdeal R) ^ n) (x.val (hcont.exponent * n)) =
          Ideal.Quotient.mk ((maximalIdeal R) ^ n) (x.val n) := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        have hc := SModEq.sub_mem.mp
          (x.property (Nat.le_mul_of_pos_left n hpos)).symm
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hc
      exact congrArg (Ideal.quotientMap ((maximalIdeal Rsh) ^ n) (algebraMap R Rsh)
        (RingHom.IsLocalHom.pow_maximalIdeal_le_comap _ n)) hc'
  have hmap := RingHom.AdicContinuous.formallySmooth_tfae
    (maximalIdeal R).fg_of_isNoetherianRing
    (maximalIdeal Rsh).fg_of_isNoetherianRing hcont
  have hformal := IsStrictHenselizationOf.formallySmoothForMaximalIdeal
    (R := R) (S := Rsh)
  have hthird := (hmap.out 0 2).mp hformal
  rw [heq] at hthird
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact hthird

section StrictBaseChange

variable [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]

/-- Lemma 15.45.3 (e) (tag `06LJ`): after using the canonical henselization comparison to make
the base completion an `Rh`-algebra, its tensor product with `Rsh` is a strict henselization of
the completed base. This is the owner-level form of
`(Rhat)sh = Rhat ⊗[Rh] Rsh`. -/
@[stacks 06LJ "(e) strict henselization after completion"]
theorem strictBaseChange_isStrictHenselization [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    IsStrictHenselizationOf (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh) := by
  let Rhat := AdicCompletion (maximalIdeal R) R
  letI : Algebra Rh Rhat := iota.toAlgHom.toRingHom.toAlgebra
  letI : HenselianRing Rhat (maximalIdeal Rhat) :=
    IsAdicComplete.henselianRing Rhat (maximalIdeal Rhat)
  letI : IsHenselizationOf Rhat Rhat :=
    { toHenselianLocalRing :=
        { is_henselian := fun f hf a ha hd =>
            HenselianRing.is_henselian f hf a ha
              ((Ideal.Quotient.mk (maximalIdeal Rhat)).isUnit_map hd) }
      toIsLocalHom := inferInstance
      isFilteredColimitOfEtale :=
        RingHom.IndEtale.ofBijective (RingHom.id Rhat) Function.bijective_id
      map_maximalIdeal := by simp
      residueField_bijective := by simpa using (Function.bijective_id :
        Function.Bijective (RingHom.id (ResidueField Rhat))) }
  let comparison : AlgHom.Local (R := R) (A := Rh) (B := Rhat) :=
    { hom := iota.toAlgHom
      isLocal := IsHenselizationOf.Completion.Comparison.isLocal iota }
  have hbase : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R Rhat)) :=
    AdicCompletion.residueField_map_bijective R
  have hmap : Ideal.map (algebraMap Rh Rsh) (maximalIdeal Rh) =
      maximalIdeal Rsh := by
    rw [← IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh),
      Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh Rsh,
      IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh)]
  have hlocal : IsLocalHom (algebraMap Rh Rsh) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap Rh Rsh)).out 2 0).mp
    rw [hmap]
  have hcomp : ((algebraMap Rh Rsh).comp (algebraMap R Rh)).IndEtale := by
    simpa [IsScalarTower.algebraMap_eq R Rh Rsh] using
      (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rsh))
  letI : IsStrictHenselizationOf Rh Rsh :=
    { toStrictHenselianLocalRing := inferInstance
      toIsLocalHom := hlocal
      isFilteredColimitOfEtale :=
        RingHom.IndEtale.of_comp (algebraMap R Rh) (algebraMap Rh Rsh)
          (IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh)) hcomp
      map_maximalIdeal := hmap }
  have h := IsStrictHenselizationOf.BaseChange.Tensor.isStrict_of_baseResidueField
    (A := R) (B := Rhat) (Ah := Rh) (Ash := Rsh) (Bh := Rhat)
    (comparison := comparison) hbase
  have halg :
      IsStrictHenselizationOf.BaseChange.Tensor.algebra comparison =
        (inferInstance : Algebra Rhat (Rhat ⊗[Rh] Rsh)) :=
    Algebra.algebra_ext _ _ (fun r => by
      change (Algebra.TensorProduct.includeLeftRingHom
        (R := Rh) (A := Rhat) (B := Rsh)) r = r ⊗ₜ[Rh] 1
      rfl)
  rw [halg] at h
  simpa [Rhat, comparison, AlgHom.Local.toAlgebra] using h

/-- The right tensor-factor map in the strict base-change model is local. This proof-only bridge
lets the canonical completion map be stated without registering a comparison-dependent global
instance. -/
theorem strictBaseChange_includeRight_isLocal [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    IsLocalHom (Algebra.TensorProduct.includeRight.toRingHom :
      Rsh →+* AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh) := by
  letI : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
    iota.toAlgHom.toRingHom.toAlgebra
  let T := AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh
  letI : IsStrictHenselizationOf (AdicCompletion (maximalIdeal R) R) T :=
    strictBaseChange_isStrictHenselization iota
  let f : Rsh →+* T := Algebra.TensorProduct.includeRight.toRingHom
  change IsLocalHom f
  have hcomp : f.comp (algebraMap R Rsh) =
      (algebraMap (AdicCompletion (maximalIdeal R) R) T).comp
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    apply RingHom.ext
    intro r
    change Algebra.TensorProduct.includeRight (algebraMap R Rsh r) = _
    rw [IsScalarTower.algebraMap_apply R Rh Rsh,
      Algebra.TensorProduct.includeRight.commutes]
    rw [IsScalarTower.algebraMap_apply Rh (AdicCompletion (maximalIdeal R) R) T]
    change algebraMap (AdicCompletion (maximalIdeal R) R) T
      (iota.toAlgHom (algebraMap R Rh r)) = _
    rw [iota.toAlgHom.commutes]
    rfl
  letI : IsLocalHom (f.comp (algebraMap R Rsh)) := by
    rw [hcomp]
    infer_instance
  apply ((IsLocalRing.local_hom_TFAE f).out 2 0).mp
  rw [← IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh), Ideal.map_map]
  exact IsLocalRing.map_maximalIdeal_le (f.comp (algebraMap R Rsh))

/-- Lemma 15.45.3 (f) (tag `06LJ`): completing the strict base-change model gives the same
completion as `Rsh`; concretely, the completion map induced by the right tensor-factor inclusion
is bijective. -/
@[stacks 06LJ "(f) completion of the strict base-change model"]
theorem strictBaseChange_completionMap_bijective [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    let T := AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh
    let _ : IsStrictHenselizationOf (AdicCompletion (maximalIdeal R) R) T :=
      strictBaseChange_isStrictHenselization iota
    let f : Rsh →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let _ : IsLocalHom f := strictBaseChange_includeRight_isLocal iota
    Function.Bijective (AdicCompletion.mapLocal f) := sorry

end StrictBaseChange

end Henselization
