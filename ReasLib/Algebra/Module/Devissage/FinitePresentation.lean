/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Module.Devissage.Complete
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars

/-!
# Finite presentation in complete module dévissages

This file records finite-presentation properties of the algebras, comparison maps, and modules
appearing in a complete module dévissage.
-/

@[expose] public section

universe u

namespace Module.Devissage.Complete

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
variable {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R}

/-- Every intermediate algebra `Bᵢ` in a complete dévissage is finitely presented over `R`. -/
theorem finitePresentationB (D : Complete R S N r) (i : Fin (D.last + 1)) :
    Algebra.FinitePresentation R (D.stage i).B := by
  exact RingHom.finitePresentation_algebraMap.mp (D.smooth i).finitePresentation

/-- If `S` is finitely presented over `R`, then the initial algebra `A₀` is finitely presented
over `R`. -/
theorem finitePresentationAFirst (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Algebra.FinitePresentation R (D.stage 0).A := by
  apply RingHom.finitePresentation_algebraMap.mp
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] using
    D.initial_finitePresentation.comp
      (RingHom.finitePresentation_algebraMap.mpr
        (inferInstance : Algebra.FinitePresentation R S.obj))

/-- Every noninitial algebra `Aᵢ` in a complete dévissage is finitely presented over `R`. -/
theorem finitePresentationASucc (D : Complete R S N r) (i : Fin D.last) :
    Algebra.FinitePresentation R (D.stage i.succ).A := by
  apply RingHom.finitePresentation_algebraMap.mp
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] using
    (D.transition_finitePresentation i).comp
      (RingHom.finitePresentation_algebraMap.mpr (finitePresentationB D i.castSucc))

/-- If `S` is finitely presented over `R`, then every stage map `Bᵢ ⟶ Aᵢ` is a ring map of
finite presentation. -/
theorem toA_finitePresentation (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] (i : Fin (D.last + 1)) :
    RingHom.FinitePresentation (D.stage i).toA.hom.toRingHom := by
  have hA : Algebra.FinitePresentation R (D.stage i).A :=
    Fin.cases (finitePresentationAFirst D) (fun j => finitePresentationASucc D j) i
  have hcomp :
      ((D.stage i).toA.hom.toRingHom.comp (algebraMap R (D.stage i).B)).FinitePresentation := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] using
      RingHom.finitePresentation_algebraMap.mpr hA
  exact hcomp.of_comp_finiteType _
    (RingHom.FiniteType.of_finitePresentation
      (RingHom.finitePresentation_algebraMap.mpr (finitePresentationB D i)))

private theorem finitePresentation_iff_finite_algebra
    (A B M : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite A B] [Algebra.FinitePresentation A B] :
    Module.FinitePresentation A M ↔ Module.FinitePresentation B M := by
  constructor
  · intro h
    letI : Module.FinitePresentation A M := h
    letI : Module.Finite B M := Module.Finite.of_restrictScalars_finite A B M
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := B) (M := M))
    let f : (s →₀ B) →ₗ[B] M := Finsupp.linearCombination B Subtype.val
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      change LinearMap.range (Finsupp.linearCombination B Subtype.val) = ⊤
      rw [Finsupp.range_linearCombination, Subtype.range_coe_subtype]
      exact hs
    apply Module.finitePresentation_of_free_of_surjective f hf
    apply Submodule.FG.of_restrictScalars A
    exact Module.FinitePresentation.fg_ker (f.restrictScalars A) hf
  · intro h
    letI : Module.FinitePresentation B M := h
    letI : Module.FinitePresentation A B :=
      Module.FinitePresentation.of_finite_of_finitePresentation A B
    exact Module.FinitePresentation.trans A M B

private theorem finitePresentation_iff_restrict_finite
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Finite) (hfp : f.FinitePresentation) (M : ModuleCat.{u} B) :
    Module.FinitePresentation A ((ModuleCat.restrictScalars f).obj M) ↔
      Module.FinitePresentation B M := by
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  letI : Module.Finite A B := hf
  letI : Algebra.FinitePresentation A B := hfp
  exact finitePresentation_iff_finite_algebra A B M

/-- Finite presentation of the source module is equivalent to finite presentation of the
initial-stage module over its `A`-algebra. -/
theorem finitePresentation_iff_firstA (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation S.obj N ↔
      Module.FinitePresentation (D.stage 0).A (D.stage 0).M := by
  obtain ⟨e⟩ := D.initialIso
  exact e.toLinearEquiv.finitePresentation_iff.trans
    (finitePresentation_iff_restrict_finite D.initial.hom.toRingHom
      (RingHom.Finite.of_surjective _ D.initial_surjective)
      D.initial_finitePresentation (D.stage 0).M.obj)

/-- At the initial stage, finite presentation over `A` is equivalent to finite presentation
after restriction of scalars to `B`. -/
theorem firstA_finitePresentation_iff_firstB (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation (D.stage 0).A (D.stage 0).M ↔
      Module.FinitePresentation (D.stage 0).B
        ((ModuleCat.restrictScalars (D.stage 0).toA.hom.toRingHom).obj
          (D.stage 0).M.obj) := by
  exact (finitePresentation_iff_restrict_finite (D.stage 0).toA.hom.toRingHom
    (D.finite_toA 0) (toA_finitePresentation D 0) (D.stage 0).M.obj).symm

/-- Finite presentation at the initial `A`-stage is equivalent to finite presentation over
both coefficient algebras at every stage. -/
theorem finitePresentation_iff_allStages (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation (D.stage 0).A (D.stage 0).M ↔
      ∀ i : Fin (D.last + 1),
        Module.FinitePresentation (D.stage i).A (D.stage i).M ∧
          Module.FinitePresentation (D.stage i).B
            ((ModuleCat.restrictScalars (D.stage i).toA.hom.toRingHom).obj
              (D.stage i).M.obj) := by
  constructor
  · intro h i
    induction i using Fin.induction with
    | zero =>
      exact ⟨h, (firstA_finitePresentation_iff_firstB D).mp h⟩
    | succ i ih =>
      have hCoker : ModuleCat.isFinitePresentation (D.stage i.castSucc).B
          (cokernel (D.stage i.castSucc).α) :=
        ModuleCat.isFinitePresentation.cokernel_of_finite _ _ (by infer_instance) ih.2
      obtain ⟨e⟩ := D.transitionIso i
      have hNext : Module.FinitePresentation (D.stage i.succ).A (D.stage i.succ).M :=
        (finitePresentation_iff_restrict_finite (D.transition i).hom.toRingHom
          (RingHom.Finite.of_surjective _ (D.transition_surjective i))
          (D.transition_finitePresentation i) (D.stage i.succ).M.obj).mp
            (e.toLinearEquiv.finitePresentation_iff.mp hCoker)
      exact ⟨hNext,
        (finitePresentation_iff_restrict_finite (D.stage i.succ).toA.hom.toRingHom
          (D.finite_toA i.succ) (toA_finitePresentation D i.succ)
          (D.stage i.succ).M.obj).mpr hNext⟩
  · intro h
    exact (h 0).1

/-- If `S` is finitely presented over `R`, finite presentation of the source module over `S`,
of the initial module over `A₀`, of its restriction to `B₀`, and of every stage module over both
`Aᵢ` and `Bᵢ` are equivalent. -/
theorem finitePresentation_tfae (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    List.TFAE
      [ Module.FinitePresentation S.obj N
      , Module.FinitePresentation (D.stage 0).A (D.stage 0).M
      , Module.FinitePresentation (D.stage 0).B
          ((ModuleCat.restrictScalars (D.stage 0).toA.hom.toRingHom).obj
            (D.stage 0).M.obj)
      , ∀ i : Fin (D.last + 1),
          Module.FinitePresentation (D.stage i).A (D.stage i).M ∧
            Module.FinitePresentation (D.stage i).B
              ((ModuleCat.restrictScalars (D.stage i).toA.hom.toRingHom).obj
                (D.stage i).M.obj)
      ] := by
  apply List.tfae_cons_cons.mpr
  refine ⟨finitePresentation_iff_firstA D, ?_⟩
  apply List.tfae_cons_cons.mpr
  refine ⟨firstA_finitePresentation_iff_firstB D, ?_⟩
  apply List.tfae_cons_cons.mpr
  exact ⟨(firstA_finitePresentation_iff_firstB D).symm.trans
    (finitePresentation_iff_allStages D), List.tfae_singleton _⟩

end Module.Devissage.Complete
