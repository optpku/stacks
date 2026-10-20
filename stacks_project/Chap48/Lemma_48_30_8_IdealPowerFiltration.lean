/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Filtration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

#check (IdealPowerFiltration.antitone :
  ∀ (I : X.IdealSheafData) (M : X.Modules),
    Antitone (fun q : ℤ ↦ idealPowerProductSubobject I M q.toNat))

#check (IdealPowerFiltration.monotone :
  ∀ (I : X.IdealSheafData) (M : X.Modules),
    Monotone (fun q : ℤᵒᵈ ↦
      idealPowerProductSubobject I M (OrderDual.ofDual q).toNat))

#check (IdealPowerFiltration.filtration :
  ∀ (I : X.IdealSheafData) (M : X.Modules), DecreasingFiltration M)

#check (IdealPowerFiltration.filtration_stage_nat :
  ∀ (I : X.IdealSheafData) (M : X.Modules) (n : ℕ),
    (IdealPowerFiltration.filtration I M).stage (n : ℤ) =
      idealPowerProductSubobject I M n)

#check (IdealPowerFiltration.map_factors :
  ∀ (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ),
    (idealPowerProductSubobject I N q.toNat).Factors
      ((idealPowerProductSubobject I M q.toNat).arrow ≫ f))

#check (IdealPowerFiltration.map_preserves :
  ∀ (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) (q : ℤ),
    ((IdealPowerFiltration.filtration I N).stage q).Factors
      (((IdealPowerFiltration.filtration I M).stage q).arrow ≫ f))

#check (IdealPowerFiltration.filtered :
  ∀ (I : X.IdealSheafData), X.Modules ⥤ FilteredObject X.Modules)

#check (IdealPowerFiltration.filtered_preservesZeroMorphisms :
  ∀ (I : X.IdealSheafData),
    (IdealPowerFiltration.filtered I).PreservesZeroMorphisms)

#check (IdealPowerFiltration.filtered_obj :
  ∀ (I : X.IdealSheafData) (M : X.Modules),
    ((IdealPowerFiltration.filtered I).obj M).obj = M)

#check (IdealPowerFiltration.filtered_map_hom :
  ∀ (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N),
    ((IdealPowerFiltration.filtered I).map f).hom = f)

#check (IdealPowerComplex.filtered :
  ∀ (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ),
    CochainComplex (FilteredObject X.Modules) ℤ)

#check (IdealPowerComplex.underlyingIso :
  ∀ (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ),
    HomologicalComplex.Filtered.underlying (IdealPowerComplex.filtered I K) ≅ K)

#check (IdealPowerComplex.underlyingIso_hom_f :
  ∀ (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ) (i : ℤ),
    (IdealPowerComplex.underlyingIso I K).hom.f i = 𝟙 (K.X i))

#check (IdealPowerComplex.stage_X :
  ∀ (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ),
    (HomologicalComplex.Filtered.Stage.complex
      (IdealPowerComplex.filtered I K) (n : ℤ)).X i =
        (idealPowerProductSubobject I (K.X i) n : X.Modules))

#check (IdealPowerComplex.stage_inclusion_f :
  ∀ (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ),
    (HomologicalComplex.Filtered.Stage.inclusion
      (IdealPowerComplex.filtered I K) (n : ℤ)).f i =
        (((IdealPowerComplex.filtered I K).X i).filtration.stage (n : ℤ)).arrow)

end AlgebraicGeometry.Scheme.Modules
