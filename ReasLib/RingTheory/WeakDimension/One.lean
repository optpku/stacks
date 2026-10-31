/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.RingTheory.Flat.Tensor
public import ReasLib.RingTheory.Flat.Ideal
public import ReasLib.RingTheory.Valuation.Locally
public import ReasLib.RingTheory.WeakDimension
import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak dimension at most one

This leaf owns the reusable characterizations of weak dimension at most one.  The individual
consequences accompany the aggregate `List.TFAE`, so downstream developments do not have to
reconstruct paths through a five-clause equivalence or install temporary instances.
@stack 092S
-/

@[expose] public section

open CategoryTheory

universe u v

namespace HasWeakDimensionLE

variable {R : Type u} [CommRing R]

/-- Weak dimension at most one makes every ideal flat. -/
@[stacks 092S "weak dimension one gives flat ideals"]
theorem ideal_flat (h : HasWeakDimensionLE R 1) (I : Ideal R) :
    Module.Flat R I := by
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype (Submodule.mkQ I)
    (by ext x; exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property)
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro x
      change (Submodule.mkQ I) x = 0 ↔ ∃ y : I, (y : R) = x
      simp [Ideal.Quotient.eq_zero_iff_mem]
    · exact Subtype.val_injective
    · exact Submodule.mkQ_surjective I
  have hR := (ModuleCat.hasTorDimensionLE_zero_iff_flat (ModuleCat.of R R)).mpr
    (inferInstance : Module.Flat R R)
  have hQ := h.hasTorDimensionLE (ModuleCat.of R (R ⧸ I))
  have hI := h.hasTorDimensionLE (ModuleCat.of R I)
  apply (ModuleCat.hasTorDimensionLE_zero_iff_flat (ModuleCat.of R I)).mp
  constructor
  · simpa [S] using
      (DerivedCategory.DerivedTensor.TorAmplitude.Lower.obj₁_of_distinguished
        hS.singleTriangle hS.singleTriangle_distinguished (a := -1)
        (by simpa [S] using hR.1) (by simpa [S] using hQ.1))
  · exact hI.2

private theorem flat_submodule_of_fg_ideals_flat
    (h : ∀ I : Ideal R, I.FG → Module.Flat R I)
    {M : Type v} [AddCommMonoid M] [Module R M]
    (hM : Module.Flat R M) (N : Submodule R M) : Module.Flat R N := by
  letI := Module.addCommMonoidToAddCommGroup R (M := M)
  letI := hM
  apply Module.Flat.iff_rTensor_injective.mpr
  intro I hI
  letI := h I hI
  apply Function.Injective.of_comp (f := N.subtype.lTensor R)
  change Function.Injective ((N.subtype.lTensor R).comp (I.subtype.rTensor N))
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap I.subtype
    Subtype.val_injective).comp
    (Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective)

/-- Under weak dimension at most one, every submodule of a flat module is flat. -/
@[stacks 092S "weak dimension one gives flat submodules"]
theorem submodule_flat (h : HasWeakDimensionLE R 1)
    {M : Type v} [AddCommMonoid M] [Module R M]
    (hM : Module.Flat R M) (N : Submodule R M) :
    Module.Flat R N :=
  flat_submodule_of_fg_ideals_flat (fun I _ ↦ ideal_flat h I) hM N

/-- Submodules of flat modules are canonically flat over a ring of weak dimension at most one. -/
@[stacks 092S "canonical flatness of submodules in weak dimension one"]
instance instSubmoduleFlat [HasWeakDimensionLE R 1]
    {M : Type v} [AddCommMonoid M] [Module R M] [Module.Flat R M]
    (N : Submodule R M) : Module.Flat R N :=
  submodule_flat inferInstance inferInstance N

/-- A ring of weak dimension at most one is locally valuation. -/
@[stacks 092S "weak dimension one gives valuation localizations"]
theorem locallyValuation (h : HasWeakDimensionLE R 1) :
    Ring.LocallyValuation R :=
  Ring.LocallyValuation.of_ideals_flat (ideal_flat h)

private theorem one_of_submodules_flat
    (h : ∀ (M : ModuleCat.{u} R) [Module.Flat R M] (N : Submodule R M),
      Module.Flat R N) : HasWeakDimensionLE R 1 := by
  constructor
  intro M
  apply ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE
  let f := Finsupp.linearCombination R (id : M → M)
  let F : Fin 2 → ModuleCat.{u} R :=
    Fin.cases (ModuleCat.of R (M →₀ R)) (fun _ ↦ ModuleCat.of R f.ker)
  refine ⟨F, ?_, (fun i ↦ ?_), ModuleCat.ofHom f, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun _ ↦ ?_) i
    · exact (inferInstance : Module.Flat R (M →₀ R))
    · exact h (ModuleCat.of R (M →₀ R)) f.ker
  · exact Fin.cases (ModuleCat.ofHom f.ker.subtype) (fun j ↦ Fin.elim0 j) i
  · exact Finsupp.linearCombination_id_surjective R M
  · intro x
    show f x = 0 ↔ ∃ y : f.ker, (y : M →₀ R) = x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · intro i
    exact Fin.elim0 i
  · exact Subtype.val_injective

/-- Weak dimension at most one is equivalent to flatness of every ideal. -/
@[stacks 092S "weak dimension one iff all ideals are flat"]
theorem one_iff_ideals_flat :
    HasWeakDimensionLE R 1 ↔ ∀ I : Ideal R, Module.Flat R I := by
  constructor
  · exact ideal_flat
  · intro h
    apply one_of_submodules_flat
    intro M hM N
    exact flat_submodule_of_fg_ideals_flat (fun I _ ↦ h I) hM N

/-- Weak dimension at most one is detected on finitely generated ideals. -/
@[stacks 092S "weak dimension one iff finitely generated ideals are flat"]
theorem one_iff_fg_ideals_flat :
    HasWeakDimensionLE R 1 ↔
      ∀ I : Ideal R, I.FG → Module.Flat R I := by
  constructor
  · intro h I _
    exact ideal_flat h I
  · intro h
    apply one_of_submodules_flat
    intro M hM N
    exact flat_submodule_of_fg_ideals_flat h hM N

/-- Weak dimension at most one is equivalent to flatness of submodules of flat modules. -/
@[stacks 092S "weak dimension one iff submodules of flat modules are flat"]
theorem one_iff_submodules_flat :
    HasWeakDimensionLE R 1 ↔
      ∀ (M : ModuleCat.{u} R) [Module.Flat R M] (N : Submodule R M),
        Module.Flat R N := by
  constructor
  · intro h M hM N
    exact submodule_flat h hM N
  · exact one_of_submodules_flat

/-- Weak dimension at most one is equivalent to having valuation rings at all prime
localizations. -/
@[stacks 092S "weak dimension one iff locally valuation"]
theorem one_iff_locallyValuation :
    HasWeakDimensionLE R 1 ↔ Ring.LocallyValuation R :=
  ⟨locallyValuation, fun h ↦ one_iff_ideals_flat.mpr h.ideal_flat⟩

/-- The ideal, submodule, and prime-local characterizations of weak dimension at most one. -/
@[stacks 092S "weak dimension one characterizations"]
theorem one_tfae :
    List.TFAE
      [ HasWeakDimensionLE R 1,
        ∀ I : Ideal R, Module.Flat R I,
        ∀ I : Ideal R, I.FG → Module.Flat R I,
        ∀ (M : ModuleCat.{u} R) [Module.Flat R M] (N : Submodule R M),
          Module.Flat R N,
        Ring.LocallyValuation R ] := by
  apply List.tfae_of_forall (HasWeakDimensionLE R 1)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact one_iff_ideals_flat.symm
  · exact one_iff_fg_ideals_flat.symm
  · exact one_iff_submodules_flat.symm
  · exact one_iff_locallyValuation.symm

end HasWeakDimensionLE
