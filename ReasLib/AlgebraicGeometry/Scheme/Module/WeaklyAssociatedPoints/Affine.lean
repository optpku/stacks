/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points on affine opens

Weak association for the sections of a quasicoherent scheme module over an
affine open agrees with weak association at the corresponding point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u v w z

/-- Torsion ideals commute with a localization map on a localized module. -/
private theorem torsionOf_localizedMap
    {R : Type u} {A : Type v} {M : Type w} {N : Type z}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (S : Submonoid R) [IsLocalization S A]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (m : M) :
    Ideal.torsionOf A N (f m) =
      (Ideal.torsionOf R M m).map (algebraMap R A) := by
  ext a
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S a
  rw [Ideal.mem_torsionOf_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  rw [← IsLocalizedModule.mk'_one S f m,
    IsLocalizedModule.mk'_smul_mk' A f,
    IsLocalizedModule.mk'_eq_zero']
  simp only [Ideal.mem_torsionOf_iff, Subtype.exists, exists_prop,
    Submonoid.smul_def, smul_smul]

/-- Weak association at a prime is equivalent to weak association at the maximal ideal after
localizing both the ring and the module at that prime. -/
private theorem isWeaklyAssociatedToModule_iff_maximalIdeal_of_isLocalizedModule
    {R : Type u} {A : Type v} {M : Type w} {N : Type z}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] [IsLocalRing A]
    (f : M →ₗ[R] N) [IsLocalizedModule p.primeCompl f] :
    Ideal.IsWeaklyAssociatedToModule R M p ↔
      Ideal.IsWeaklyAssociatedToModule A N (IsLocalRing.maximalIdeal A) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨f m, ?_⟩
    rw [torsionOf_localizedMap p.primeCompl f m,
      IsLocalization.minimalPrimes_map p.primeCompl A]
    simpa only [Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A p] using hm
  · rintro ⟨n, hn⟩
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective p.primeCompl f n
    refine ⟨m, ?_⟩
    have htorsion :
        Ideal.torsionOf A N (IsLocalizedModule.mk' f m s) =
          Ideal.torsionOf A N (f m) := by
      ext a
      simp only [Ideal.mem_torsionOf_iff]
      constructor
      · intro ha
        calc
          a • f m = a • (s.1 • IsLocalizedModule.mk' f m s) := by
            exact congrArg (a • ·) (IsLocalizedModule.mk'_cancel' f m s).symm
          _ = s.1 • (a • IsLocalizedModule.mk' f m s) := smul_comm _ _ _
          _ = 0 := by rw [ha, smul_zero]
      · intro ha
        apply (IsLocalizedModule.smul_injective f s)
        calc
          s.1 • (a • IsLocalizedModule.mk' f m s) =
              a • (s.1 • IsLocalizedModule.mk' f m s) := smul_comm _ _ _
          _ = a • f m :=
            congrArg (a • ·) (IsLocalizedModule.mk'_cancel' f m s)
          _ = 0 := ha
          _ = s.1 • 0 := (smul_zero _).symm
    change IsLocalRing.maximalIdeal A ∈
      (Ideal.torsionOf A N (IsLocalizedModule.mk' f m s)).minimalPrimes at hn
    rw [htorsion, torsionOf_localizedMap p.primeCompl f m,
      IsLocalization.minimalPrimes_map p.primeCompl A] at hn
    simpa only [Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A p] using hn

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a quasicoherent scheme module on an affine open, a prime of the section
ring is weakly associated to the module of sections exactly when the
corresponding point is weakly associated to the scheme module. -/
@[stacks 056M]
theorem mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    p.asIdeal ∈ weaklyAssociatedPrimes (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ ℱ.weakAss := by
  let y : X := hU.fromSpec p
  have hy : y ∈ U := (hU.isoSpec.inv p).2
  -- Local instance justification (proof-local temporary data): use the canonical section-to-stalk algebra at `y`.
  letI : Algebra (Γ(X, U)) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  -- Local instance justification (proof-local temporary data): use the affine localization description of the stalk at `y`.
  letI : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
    hU.isLocalization_stalk' p hy
  let f := sectionToStalk ℱ U y hy
  have hf : IsLocalizedModule p.asIdeal.primeCompl f :=
    isLocalizedModule_sectionToStalk ℱ hU p hy
  -- Local instance justification (defeq pin): view the target stalk module over the affine section ring.
  letI : Module Γ(X, U) (RingedSpace.stalkModuleCat ℱ y) :=
    Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk y))
  -- Local instance justification (defeq pin): record the canonical scalar tower for the final localization comparison.
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk y)
      (RingedSpace.stalkModuleCat ℱ y) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  change Ideal.IsWeaklyAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal ↔
    Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk y)
      (RingedSpace.stalkModuleCat ℱ y) (IsLocalRing.maximalIdeal _)
  exact isWeaklyAssociatedToModule_iff_maximalIdeal_of_isLocalizedModule
    p.asIdeal f

end AlgebraicGeometry.Scheme.Modules
