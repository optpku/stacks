/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Module
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

variable {A B : CosimplicialObject CommRingCat.{u}}

/-- The morphism of commutative-ring presheaves induced by a cosimplicial ring morphism. -/
abbrev commRingMap (f : A ⟶ B) : cosimplicialCommRing A ⟶ cosimplicialCommRing B :=
  Functor.whiskerLeft (unopUnop SimplexCategory) f

/-- The components of the induced ring-presheaf morphism are the original ring maps. -/
theorem commRingMap_app (f : A ⟶ B) (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (commRingMap f).app X = f.app (unop (unop X)) :=
  rfl

/-- A cosimplicial ring morphism commutes with the underlying ring structure maps. -/
theorem commRingMap_naturality (f : A ⟶ B)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    ((commRingMap f).app Y).hom.comp ((moduleRingPresheaf A).map g).hom =
      ((moduleRingPresheaf B).map g).hom.comp ((commRingMap f).app X).hom :=
  PresheafOfModules.SameSiteTensorExtension.square (commRingMap f) g

namespace CosimplicialModule

/-- The scalar-extension structure map obtained by extending the source degree and
restricting the target degree along the cosimplicial ring maps. -/
def extensionStructureMap (f : A ⟶ B)
    (K : PresheafOfModules.{u} (moduleRingPresheaf A))
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (ModuleCat.extendScalars ((commRingMap f).app X).hom).obj (K.obj X) ⟶
      (ModuleCat.restrictScalars ((moduleRingPresheaf B).map g).hom).obj
        ((ModuleCat.extendScalars ((commRingMap f).app Y).hom).obj (K.obj Y)) :=
  PresheafOfModules.SameSiteTensorExtension.restriction (commRingMap f) K g

end CosimplicialModule

/-- Degreewise scalar extension of a module over a cosimplicial ring. -/
def extendScalarsObj (f : A ⟶ B) (K : PresheafOfModules.{u} (moduleRingPresheaf A)) :
    PresheafOfModules.{u} (moduleRingPresheaf B) :=
  PresheafOfModules.SameSiteTensorExtension.obj (commRingMap f) K

/-- Degreewise scalar extension of a morphism of cosimplicial modules. -/
def extendScalarsHom (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M) :
    extendScalarsObj f K ⟶ extendScalarsObj f M :=
  PresheafOfModules.SameSiteTensorExtension.map (commRingMap f) φ

/-- The components of scalar extension are the ordinary scalar-extension maps. -/
theorem extendScalarsHom_app (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M)
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (extendScalarsHom f φ).app X =
      (ModuleCat.extendScalars ((commRingMap f).app X).hom).map (φ.app X) :=
  rfl

namespace CosimplicialModule

/-- The coefficient morphism for restriction of scalars along a cosimplicial ring map. -/
abbrev coefficients (f : A ⟶ B) : moduleRingPresheaf A ⟶ moduleRingPresheaf B :=
  PresheafOfModules.SameSiteTensorExtension.ringMap (commRingMap f)

/-- Degreewise scalar extension, using the public same-site tensor construction. -/
def extension (f : A ⟶ B) :
    PresheafOfModules.{u} (moduleRingPresheaf A) ⥤
      PresheafOfModules.{u} (moduleRingPresheaf B) :=
  PresheafOfModules.SameSiteTensorExtension.functor (commRingMap f)

/-- The functor retains the degreewise object interface. -/
theorem extension_obj (f : A ⟶ B) (K : PresheafOfModules.{u} (moduleRingPresheaf A)) :
    (extension f).obj K = extendScalarsObj f K :=
  rfl

/-- The functor retains the degreewise morphism interface. -/
theorem extension_map (f : A ⟶ B)
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ : K ⟶ M) :
    (extension f).map φ = extendScalarsHom f φ :=
  rfl

/-- The degreewise tensor/restriction adjunction, specialized from the same-site owner. -/
def extensionRestrictionAdjunction (f : A ⟶ B) :
    extension f ⊣ PresheafOfModules.restrictScalars (coefficients f) :=
  PresheafOfModules.SameSiteTensorExtension.adjunction (commRingMap f)

/-- Degreewise tensor extension and abstract pullback extension are canonically isomorphic.
The right-adjoint instance is needed only to name the abstract extension functor. -/
def sharedComparison (f : A ⟶ B)
    [(PresheafOfModules.pushforward.{u}
      (PresheafOfModules.ChangeOfRings.homOverId (coefficients f))).IsRightAdjoint] :
    extension f ≅ PresheafOfModules.ChangeOfRings.extension (coefficients f) :=
  (extensionRestrictionAdjunction f).leftAdjointUniq
    (PresheafOfModules.ChangeOfRings.extensionRestrictionAdjunction (coefficients f))

end CosimplicialModule
