/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel.Opcycles
public import ReasLib.Algebra.Homology.HomologicalComplex.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential cokernels under restriction of scalars

Restriction of scalars is exact, so restricting an incoming differential cokernel agrees with
taking the incoming differential cokernel after termwise restriction.  This leaf exposes the
canonical comparison needed by relative flatness arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CochainComplex.DifferentialCokernel

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- Stacks `03B8`: restriction of scalars commutes with the cokernel of an incoming cochain differential. -/
@[stacks 03B8 "restriction preserves differential cokernels", stacks 08G0]
noncomputable def restrictScalarsIso
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).obj (E.differentialCokernel n) ≅
      CochainComplex.differentialCokernel (E.restrictScalarsAlong σ) n :=
  PreservesCokernel.iso (ModuleCat.restrictScalars σ) (E.d (n - 1) n)

/-- Stacks `03B8`: restriction of scalars carries the original cokernel projection to the restricted-complex
cokernel projection through `restrictScalarsIso`. -/
@[reassoc (attr := simp), stacks 03B8 "projection compatibility for restricted cokernels"]
theorem map_π_restrictScalarsIso_hom
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).map (cokernel.π (E.d (n - 1) n)) ≫
        (restrictScalarsIso σ E n).hom =
      cokernel.π ((E.restrictScalarsAlong σ).d (n - 1) n) := sorry

/-- Stacks `03B8`: the inverse restricted-cokernel comparison recovers the mapped original projection. -/
@[reassoc (attr := simp), stacks 03B8 "inverse projection compatibility for restricted cokernels"]
theorem π_restrictScalarsIso_inv
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    cokernel.π ((E.restrictScalarsAlong σ).d (n - 1) n) ≫
        (restrictScalarsIso σ E n).inv =
      (ModuleCat.restrictScalars σ).map (cokernel.π (E.d (n - 1) n)) := sorry

/-- Stacks `03B8`: the differential-cokernel comparison for restriction of scalars is natural in
cochain maps. -/
@[reassoc, stacks 03B8 "naturality of restricted differential cokernels"]
theorem restrictScalarsIso_hom_naturality
    (σ : R →+* A) {E F : CochainComplex (ModuleCat A) ℤ} (f : E ⟶ F) (n : ℤ) :
    (ModuleCat.restrictScalars σ).map (differentialCokernelMap f n) ≫
        (restrictScalarsIso σ F n).hom =
      (restrictScalarsIso σ E n).hom ≫
        differentialCokernelMap (HomologicalComplex.restrictScalarsMap σ f) n := sorry

/-- Stacks `03B8`: restriction of scalars commutes with the canonical opcycles object. -/
@[stacks 03B8 "restriction preserves opcycles"]
noncomputable def restrictScalarsOpcyclesIso
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).obj (E.opcycles n) ≅
      (E.restrictScalarsAlong σ).opcycles n :=
  (ModuleCat.restrictScalars σ).mapIso (E.opcyclesIsoCokernel n) ≪≫
    restrictScalarsIso σ E n ≪≫
      (CochainComplex.opcyclesIsoCokernel (E.restrictScalarsAlong σ) n).symm

/-- Stacks `03B8`: the opcycles projection is preserved by restriction of scalars. -/
@[reassoc (attr := simp), stacks 03B8 "opcycles projection under restriction"]
theorem map_pOpcycles_restrictScalarsOpcyclesIso_hom
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars σ).map (E.pOpcycles n) ≫
        (restrictScalarsOpcyclesIso σ E n).hom =
      (E.restrictScalarsAlong σ).pOpcycles n := sorry

/-- Stacks `03B8`: the inverse restricted-opcycles comparison recovers the mapped original projection. -/
@[reassoc (attr := simp), stacks 03B8 "inverse opcycles projection under restriction"]
theorem pOpcycles_restrictScalarsOpcyclesIso_inv
    (σ : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (n : ℤ) :
    (E.restrictScalarsAlong σ).pOpcycles n ≫
        (restrictScalarsOpcyclesIso σ E n).inv =
      (ModuleCat.restrictScalars σ).map (E.pOpcycles n) := sorry

/-- Stacks `03B8`: the opcycles comparison for restriction of scalars is natural in cochain maps. -/
@[reassoc, stacks 03B8 "naturality of restricted opcycles"]
theorem restrictScalarsOpcyclesIso_hom_naturality
    (σ : R →+* A) {E F : CochainComplex (ModuleCat A) ℤ} (f : E ⟶ F) (n : ℤ) :
    (ModuleCat.restrictScalars σ).map (HomologicalComplex.opcyclesMap f n) ≫
        (restrictScalarsOpcyclesIso σ F n).hom =
      (restrictScalarsOpcyclesIso σ E n).hom ≫
        HomologicalComplex.opcyclesMap (HomologicalComplex.restrictScalarsMap σ f) n := sorry

end CochainComplex.DifferentialCokernel
