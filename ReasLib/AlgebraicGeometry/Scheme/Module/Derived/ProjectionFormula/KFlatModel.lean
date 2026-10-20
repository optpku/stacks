/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor.Instances
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.KFlat

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.DerivedCategory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula

/-- The homotopy-to-derived localization used by fixed-right tensoring is the canonical
localization at quasi-isomorphisms. -/
theorem homotopyLocalization_isLocalization (X : Scheme.{u}) :
    (DerivedTensor.Right.localization (C := X.Modules)).IsLocalization
      (DerivedTensor.Right.qis (C := X.Modules)) :=
  inferInstanceAs ((DerivedCategory.Qh (C := X.Modules)).IsLocalization
    (HomotopyCategory.quasiIso X.Modules (up ℤ)))

/-- A selected K-flat replacement of a homotopy complex of modules on a scheme. -/
noncomputable def kFlatResolution (X : Scheme.{u})
    [h_resolutions : HomotopyCategory.KFlat.HasResolutions X.Modules]
    (K : HomotopyCategory X.Modules (up ℤ)) :
    HomotopyCategory.KFlat X.Modules :=
  (Classical.choice (h_resolutions K)).X₁

/-- The comparison from the selected K-flat replacement to its source complex. -/
noncomputable def kFlatResolutionCounit (X : Scheme.{u})
    [h_resolutions : HomotopyCategory.KFlat.HasResolutions X.Modules]
    (K : HomotopyCategory X.Modules (up ℤ)) :
    (kFlatResolution X K).obj ⟶ K :=
  (Classical.choice (h_resolutions K)).w

/-- The comparison from the selected K-flat replacement is a quasi-isomorphism. -/
theorem kFlatResolutionCounit_quasiIso (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    (K : HomotopyCategory X.Modules (up ℤ)) :
    HomotopyCategory.quasiIso X.Modules (up ℤ)
      (kFlatResolutionCounit X K) := sorry

/-- The selected K-flat replacement and its source have canonically isomorphic images in the
derived category. -/
noncomputable def kFlatResolutionIso (X : Scheme.{u})
    [h_resolutions : HomotopyCategory.KFlat.HasResolutions X.Modules]
    (K : HomotopyCategory X.Modules (up ℤ)) :
    (DerivedCategory.KFlat.localizationFunctor.obj (kFlatResolution X K) :
        RingedSpace.ModuleDerived X.toRingedSpace) ≅ DerivedCategory.Qh.obj K :=
  Localization.isoOfHom DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    (kFlatResolutionCounit X K)
    (Classical.choice (h_resolutions K)).hw

/-- Compare a derived module with the localization of the selected K-flat replacement of its
canonical complex representative. -/
noncomputable def kFlatTensorRepresentativeIso (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    E ≅ DerivedCategory.KFlat.localizationFunctor.obj
      (kFlatResolution X (DerivedTensor.Right.KFlat.representative E)) :=
  (DerivedTensor.Right.representativeIso E).symm ≪≫
    (kFlatResolutionIso X (DerivedTensor.Right.KFlat.representative E)).symm

/-- The objectwise counit comparing ambient derived tensoring with the canonical fixed-right
derived tensor source, using selected K-flat replacements. -/
noncomputable def kFlatTensorCounitApp (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends (C := X.Modules)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization (C := X.Modules)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : HomotopyCategory X.Modules (up ℤ)) :
    ((DerivedCategory.Qh.obj K : RingedSpace.ModuleDerived X.toRingedSpace) ⊗ E) ⟶
      (DerivedTensor.Right.sourceFunctor E).obj K :=
  let R := kFlatResolution X K
  let R_E := kFlatResolution X (DerivedTensor.Right.KFlat.representative E)
  ((kFlatResolutionIso X K).inv ⊗ₘ (kFlatTensorRepresentativeIso X E).hom) ≫
    (DerivedCategory.KFlat.mapTensorIso R R_E).hom ≫
    DerivedCategory.Qh.map
      ((Functor.Monoidal.μIso (HomotopyCategory.kFlat X.Modules).ι R R_E).inv ≫
        (kFlatResolutionCounit X K ⊗ₘ
          kFlatResolutionCounit X (DerivedTensor.Right.KFlat.representative E))) ≫
    (DerivedTensor.Right.sourceFunctorIso E).hom.app K

/-- The selected K-flat counit is natural in the homotopy complex. -/
noncomputable def kFlatTensorCounit (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends (C := X.Modules)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization (C := X.Modules)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    DerivedTensor.Right.localization (C := X.Modules) ⋙
        MonoidalCategory.tensorRight E ⟶
      DerivedTensor.Right.sourceFunctor E where
  app := kFlatTensorCounitApp X E
  naturality := fun _ _ _ ↦ sorry

/-- The ambient tensor functor equipped with the selected K-flat counit is a fixed-right
left-derived tensor model. -/
theorem kFlatTensorCounit_isLeftDerived (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends (C := X.Modules)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization (C := X.Modules)]
    [(DerivedTensor.Right.localization (C := X.Modules)).IsLocalization
      (DerivedTensor.Right.qis (C := X.Modules))]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    @Functor.IsLeftDerivedFunctor
      (HomotopyCategory X.Modules (up ℤ))
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (RingedSpace.ModuleDerived X.toRingedSpace)
      _ _ _ (MonoidalCategory.tensorRight E)
      (DerivedTensor.Right.sourceFunctor E)
      (DerivedTensor.Right.localization (C := X.Modules))
      (kFlatTensorCounit X E)
      (DerivedTensor.Right.qis (C := X.Modules))
      (homotopyLocalization_isLocalization X) := sorry

/-- The explicit ambient fixed-right derived tensor model supplied by selected K-flat
replacements. -/
noncomputable def kFlatTensorModel (X : Scheme.{u})
    [HomotopyCategory.KFlat.HasResolutions X.Modules]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [HomotopyCategory.KFlat.TensorDescends (C := X.Modules)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [DerivedCategory.KFlat.IsLocalization (C := X.Modules)]
    [(DerivedTensor.Right.localization (C := X.Modules)).IsLocalization
      (DerivedTensor.Right.qis (C := X.Modules))] :
    DerivedTensor.Right.Monoidal.Model (C := X.Modules) where
  counit := kFlatTensorCounit X
  isLeftDerived := kFlatTensorCounit_isLeftDerived X

end AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
