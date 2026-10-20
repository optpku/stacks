/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport

/-!
# Strict transforms

This file constructs the strict transform of a module sheaf relative to a morphism and an ideal
sheaf on the target of that morphism. The module strict transform is the quotient by sections
supported on the pulled-back closed subset, and the scheme strict transform is cut out by the
corresponding ideal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S S' X : Scheme.{u}}
variable (b : S' ⟶ S)

/-- The fiber-product ambient scheme for a strict-transform construction. -/
abbrev strictTransformAmbient (f : X ⟶ S) : Scheme.{u} :=
  pullback f b

/-- The closed subset obtained by pulling an ideal-sheaf support back to the strict-transform
ambient scheme along its second projection. -/
abbrev strictTransformPullbackSupport
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    Closeds (strictTransformAmbient b f) :=
  (E.comap (pullback.snd f b)).support

/-- The structure sheaf on the ambient fiber product of a strict-transform construction. -/
private abbrev strictTransformRingSheaf (f : X ⟶ S) :
    TopCat.Sheaf RingCat.{u} (strictTransformAmbient b f) :=
  (strictTransformAmbient b f).ringCatSheaf

/-- The category of module sheaves on the ambient fiber product of a strict-transform
construction. -/
private abbrev strictTransformModuleCat (f : X ⟶ S) :=
  (strictTransformAmbient b f).Modules

/-- Pullback of module sheaves to the ambient fiber product of a strict-transform construction. -/
abbrev strictTransformPullbackFunctor (f : X ⟶ S) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  RingedSpace.Hom.pullback (pullback.fst f b).toShHom

/-- The subobject of a module sheaf consisting of sections supported on the pulled-back closed
subset. -/
noncomputable abbrev strictTransformSupportedSubsheaf
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : (strictTransformAmbient b f).Modules) :
    Subobject ℱ :=
  SheafOfModules.ClosedSubset.SectionsWithSupport.subsheaf
    (strictTransformAmbient b f).ringCatSheaf (strictTransformPullbackSupport b E f) ℱ

/-- The strict-transform supported subobject is the canonical closed-support subobject. -/
theorem strictTransformSupportedSubsheaf_eq_closedSupport
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : (strictTransformAmbient b f).Modules) :
    strictTransformSupportedSubsheaf b E f ℱ =
      SheafOfModules.ClosedSubset.SectionsWithSupport.subsheaf
        (strictTransformAmbient b f).ringCatSheaf (strictTransformPullbackSupport b E f) ℱ :=
  rfl

/-- Pullback followed by the functor of sections supported on the pulled-back closed subset. -/
noncomputable def strictTransformSupportedSectionsFunctor
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  strictTransformPullbackFunctor b f ⋙
    SheafOfModules.ClosedSubset.SectionsWithSupport.ambientFunctor
      (strictTransformAmbient b f).ringCatSheaf (strictTransformPullbackSupport b E f)

/-- The natural inclusion of supported sections into the pulled-back module sheaf. -/
noncomputable def strictTransformSupportedSectionsInclusion
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformSupportedSectionsFunctor b E f ⟶
      strictTransformPullbackFunctor b f :=
  Functor.whiskerLeft (strictTransformPullbackFunctor b f)
      (SheafOfModules.ClosedSubset.SectionsWithSupport.ambientInclusion
        (strictTransformAmbient b f).ringCatSheaf (strictTransformPullbackSupport b E f)) ≫
    (Functor.rightUnitor (strictTransformPullbackFunctor b f)).hom

/-- The strict-transform functor is the functor-category cokernel of the natural inclusion of
supported sections into pullback. -/
noncomputable def strictTransformFunctor
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  cokernel (strictTransformSupportedSectionsInclusion b E f)

/-- The strict transform of a module sheaf is its pullback modulo the sections supported on the
pulled-back closed subset. -/
noncomputable abbrev strictTransformModule
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules) :
    (strictTransformAmbient b f).Modules :=
  (strictTransformFunctor b E f).obj ℱ

/-- The strict transform of a finite-type module sheaf is finite type. -/
noncomputable instance strictTransformModule_isFiniteType
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsFiniteType] :
    (strictTransformModule b E f ℱ).IsFiniteType := sorry

/-- The canonical natural quotient map from pullback to the strict-transform functor. -/
noncomputable def strictTransformπNat
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformPullbackFunctor b f ⟶ strictTransformFunctor b E f :=
  cokernel.π (strictTransformSupportedSectionsInclusion b E f)

/-- The canonical quotient map from the pullback of a module sheaf to its strict transform. -/
noncomputable abbrev strictTransformπ
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules) :
    (strictTransformPullbackFunctor b f).obj ℱ ⟶ strictTransformModule b E f ℱ :=
  (strictTransformπNat b E f).app ℱ

/-- Sections supported on the pulled-back effective Cartier divisor form a quasicoherent
subsheaf of a quasicoherent module sheaf. -/
noncomputable instance strictTransformSupportedSubsheaf_isQuasicoherent
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : (strictTransformAmbient b f).Modules)
    [IsEffectiveCartierDivisor E.subschemeι] [ℱ.IsQuasicoherent] :
    (strictTransformSupportedSubsheaf b E f ℱ :
      (strictTransformAmbient b f).Modules).IsQuasicoherent :=
  sorry

/-- The strict transform of a quasicoherent module sheaf along an effective Cartier divisor is
quasicoherent. -/
noncomputable instance strictTransformModule_isQuasicoherent
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules)
    [IsEffectiveCartierDivisor E.subschemeι] [ℱ.IsQuasicoherent] :
    (strictTransformModule b E f ℱ).IsQuasicoherent :=
  sorry

/-- The ideal sheaf whose affine components consist of structure-sheaf sections supported on
the pulled-back closed subset. -/
noncomputable def strictTransformIdealSheafData
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    (strictTransformAmbient b f).IdealSheafData :=
  let I : Subobject
      (SheafOfModules.unit (strictTransformAmbient b f).ringCatSheaf :
        (strictTransformAmbient b f).Modules) :=
    strictTransformSupportedSubsheaf b E f
      (SheafOfModules.unit (strictTransformAmbient b f).ringCatSheaf :
        (strictTransformAmbient b f).Modules)
  Scheme.IdealSheafData.ofIdeals fun U : (strictTransformAmbient b f).affineOpens ↦
    SheafOfModules.Subobject.sections I (op U.1)

/-- On every affine open, the ideal cutting out the strict transform along an effective Cartier
divisor is exactly the image of the supported-section subsheaf. -/
theorem strictTransformIdealSheafData_ideal
    (E : S'.IdealSheafData) (f : X ⟶ S)
    [IsEffectiveCartierDivisor E.subschemeι]
    (U : (strictTransformAmbient b f).affineOpens) :
    (strictTransformIdealSheafData b E f).ideal U =
      SheafOfModules.Subobject.sections
        (strictTransformSupportedSubsheaf b E f
          (SheafOfModules.unit (strictTransformAmbient b f).ringCatSheaf :
            (strictTransformAmbient b f).Modules))
        (op U.1) :=
  sorry

/-- The strict-transform scheme is the closed subscheme cut out by the supported-section ideal
on the ambient fiber product. -/
noncomputable def strictTransform
    (E : S'.IdealSheafData) (f : X ⟶ S) : Scheme.{u} :=
  (strictTransformIdealSheafData b E f).subscheme

end

end AlgebraicGeometry
