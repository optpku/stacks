/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback.FinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InternalHom.Adjunction

/-! # Étale inverse image and internal Hom -/

@[expose] public section

open CategoryTheory CategoryTheory.Functor.LaxMonoidal CategoryTheory.MonoidalCategory
open FiberedCategoryOver.Groupoids SheafOfModules.RingedSite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- The sectionwise tensor comparison sends a tensor of inverse-image sections
to its image in the inverse image of the sheafified tensor. -/
def etaleModuleInverseImage_tensorComparison_app (f : X ⟶ Y) (H F : etaleModules Y)
    (U : X.totalᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj
        ((etaleModuleInverseImage f).obj H).val
        ((etaleModuleInverseImage f).obj F).val).obj U ⟶
      ((etaleModuleInverseImage f).obj (moduleTensorEtale H F)).val.obj U :=
  let coeff : ((commEtaleStructureSheaf X).obj.obj U : Type u) →+*
      ((commEtaleStructureSheaf Y).obj.obj ((toFunctor f).op.obj U) : Type u) :=
    ((commEtaleStructureSheafIso f).inv.hom.app U).hom
  let toScalars (K : etaleModules Y) :
      ((etaleModuleInverseImage f).obj K).val.obj U ⟶
        (ModuleCat.restrictScalars coeff).obj (K.val.obj ((toFunctor f).op.obj U)) :=
    ModuleCat.ofHom (R := (commEtaleStructureSheaf X).obj.obj U)
      (X := ((etaleModuleInverseImage f).obj K).val.obj U)
      (Y := (ModuleCat.restrictScalars coeff).obj (K.val.obj ((toFunctor f).op.obj U)))
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let fromScalars (K : etaleModules Y) :
      (ModuleCat.restrictScalars coeff).obj (K.val.obj ((toFunctor f).op.obj U)) ⟶
        ((etaleModuleInverseImage f).obj K).val.obj U :=
    ModuleCat.ofHom (R := (commEtaleStructureSheaf X).obj.obj U)
      (X := (ModuleCat.restrictScalars coeff).obj (K.val.obj ((toFunctor f).op.obj U)))
      (Y := ((etaleModuleInverseImage f).obj K).val.obj U)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  tensorHom (toScalars H) (toScalars F) ≫
    μ (ModuleCat.restrictScalars coeff)
      (H.val.obj ((toFunctor f).op.obj U)) (F.val.obj ((toFunctor f).op.obj U)) ≫
    (ModuleCat.restrictScalars coeff).map
      ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf Y)
          (PresheafOfModules.Monoidal.tensorObj H.val F.val)).app
          ((toFunctor f).op.obj U) ≫
        (etalePointwiseTensorSheafify_iso H F).hom.val.app ((toFunctor f).op.obj U)) ≫
    fromScalars (moduleTensorEtale H F)

/-- The canonical tensor comparison for étale module inverse image is induced
by the sectionwise comparison and sheafification. -/
def etaleModuleInverseImage_tensorComparison (f : X ⟶ Y) (H F : etaleModules Y) :
    moduleTensorEtale ((etaleModuleInverseImage f).obj H)
      ((etaleModuleInverseImage f).obj F) ⟶
      (etaleModuleInverseImage f).obj (moduleTensorEtale H F) :=
  (etalePointwiseTensorSheafify_iso ((etaleModuleInverseImage f).obj H)
      ((etaleModuleInverseImage f).obj F)).inv ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u} (commEtaleStructureSheaf X)
      (PresheafOfModules.Monoidal.tensorObj
        ((etaleModuleInverseImage f).obj H).val ((etaleModuleInverseImage f).obj F).val)
      ((etaleModuleInverseImage f).obj (moduleTensorEtale H F))).symm
      { app U := etaleModuleInverseImage_tensorComparison_app f H F U
        naturality := sorry }

/-- Étale inverse image has a canonical comparison with internal Hom from a
finitely presented module. -/
def moduleSheafHomOnEtale_pullback (f : X ⟶ Y) (F G : etaleModules Y)
    [F.IsFinitePresentation] :
    (etaleModuleInverseImage f).obj (moduleSheafHomEtale F G) ⟶
      moduleSheafHomEtale ((etaleModuleInverseImage f).obj F)
        ((etaleModuleInverseImage f).obj G) :=
  (moduleSheafHomOnEtale_homEquiv ((etaleModuleInverseImage f).obj F)
    ((etaleModuleInverseImage f).obj G)
    ((etaleModuleInverseImage f).obj (moduleSheafHomEtale F G))).symm
      (etaleModuleInverseImage_tensorComparison f (moduleSheafHomEtale F G) F ≫
        (etaleModuleInverseImage f).map
          (moduleSheafHomOnEtale_homEquiv F G (moduleSheafHomEtale F G) (𝟙 _)))

end AlgebraicGeometry.GroupoidsOver
