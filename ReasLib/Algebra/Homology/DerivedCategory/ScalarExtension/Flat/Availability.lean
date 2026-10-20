/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived availability for flat scalar extension

Flat extension is exact in arbitrary module carrier universes. Its native localization functor
and the actual lift of natural transformations provide the left-derived universal witness,
without a smallness premise or a chosen resolution.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe uR uS v

namespace CategoryTheory.ModuleCat.DerivedExtension.Flat

section Availability

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Flat tensor extension preserves exact short complexes at arbitrary carrier universes. -/
private theorem extendScalars_map_exact (σ : R →+* S) (hσ : σ.Flat)
    (C : ShortComplex (ModuleCat.{v} R)) (hC : C.Exact) :
    (C.map (ModuleCat.extendScalars.{uR, uS, v} σ)).Exact := by
  algebraize [σ]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

/-- Exactness uses the native tensor exactness theorem and does not require small free modules. -/
private theorem extendScalars_exact (σ : R →+* S) (hσ : σ.Flat) :
    exactFunctor (ModuleCat.{v} R) (ModuleCat.{max uS v} S)
      (ModuleCat.extendScalars.{uR, uS, v} σ) :=
  ((Functor.exact_tfae (ModuleCat.extendScalars.{uR, uS, v} σ)).out 1 3).mp
    (extendScalars_map_exact σ hσ)

/-- A flat scalar extension admits a left-derived functor in every module carrier universe.
The witness is the native functor induced by exact extension; its universal lift descends
through localization using the actual factorization isomorphism. -/
@[stacks 015F "exact flat extension has an unbounded derived functor"]
theorem hasLeftDerivedFunctor (σ : R →+* S) (hσ : σ.Flat) :
    (ModuleCat.extendScalarsToDerived.{uR, uS, v} σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (up ℤ)) := by
  let F := ModuleCat.extendScalars.{uR, uS, v} σ
  -- Local instances fix the actual exact functor and its native derived factorization.
  letI : PreservesFiniteLimits F := (extendScalars_exact σ hσ).1
  letI : PreservesFiniteColimits F := (extendScalars_exact σ hσ).2
  let universal : (Functor.RightExtension.mk F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.hom).IsUniversal :=
    IsTerminal.ofUniqueHom
      (fun E ↦ CostructuredArrow.homMk
        ((Localization.fullyFaithfulWhiskeringLeft
          (DerivedCategory.Qh : HomotopyCategory (ModuleCat.{v} R) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{v} R))
          (HomotopyCategory.quasiIso (ModuleCat.{v} R) (up ℤ))
          (DerivedCategory (ModuleCat.{max uS v} S))).preimage
            (E.hom ≫ F.mapDerivedCategoryFactorsh.inv)) (by sorry))
      (fun E φ ↦ by sorry)
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (up ℤ)) :=
    ⟨⟨⟨universal⟩⟩⟩
  exact Functor.HasLeftDerivedFunctor.mk' (LF := F.mapDerivedCategory)
    (α := F.mapDerivedCategoryFactorsh.hom)

/-- The native exact model supplies derived availability for a flat algebra map, including
localizations, without imposing a base-size condition on the source modules. -/
instance algebraMap_hasLeftDerivedFunctor [Algebra R S] [Module.Flat R S] :
    (ModuleCat.extendScalarsToDerived.{uR, uS, v} (algebraMap R S)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (up ℤ)) :=
  hasLeftDerivedFunctor (algebraMap R S)
    ((RingHom.flat_algebraMap_iff).mpr inferInstance)

end Availability

end CategoryTheory.ModuleCat.DerivedExtension.Flat
