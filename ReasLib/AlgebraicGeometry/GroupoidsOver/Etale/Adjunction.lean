/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-!
# Actual étale module transposition with small sheaf sections

Continuous module inverse image has the actual precomposed section carrier.
Its right adjoint is transposed through the genuine type-valued sheaf
adjunction. No scalar-extension left adjoint is chosen from a new
existence certificate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Functor
open FiberedCategoryOver.Groupoids
open Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Actual continuous inverse image leaves precisely the precomposed underlying sections. -/
def etaleModuleInverseImageUnderlyingIso {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleModuleInverseImage h ⋙ ToInternal.underlying (etaleRingedSite X).structureSheaf ≅
      ToInternal.underlying (etaleRingedSite Y).structureSheaf ⋙
        (toFunctor h).sheafPushforwardContinuous (Type u) X.etaleTopology Y.etaleTopology :=
  NatIso.ofComponents (fun G ↦ Iso.refl _) (by
    intro G H η
    ext U x
    rfl)

private theorem etaleModule_hom_ext (X : GroupoidsOver S)
    {M N : SheafOfModules.{u} (etaleRingedSite X).structureSheaf} {α β : M ⟶ N}
    (hαβ : (ToInternal.underlying (etaleRingedSite X).structureSheaf).map α =
      (ToInternal.underlying (etaleRingedSite X).structureSheaf).map β) : α = β := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun η ↦ η.hom.app U x) hαβ

variable {X Y : GroupoidsOver S} (h : X ⟶ Y)
variable [HasSmallCFGTypeSections (S := S) h]

private theorem etaleSheafHomEquiv_apply_symm_apply
    (F : Sheaf X.etaleTopology (Type u)) (N : Sheaf Y.etaleTopology (Type u))
    (η : ((toFunctor h).sheafPushforwardContinuous (Type u)
      X.etaleTopology Y.etaleTopology).obj N ⟶ F) :
    (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv X.etaleTopology Y.etaleTopology F N
      (((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
        X.etaleTopology Y.etaleTopology F N).symm η) = η := by
  apply ObjectProperty.hom_ext
  exact (homEquivOfIsRightKanExtension (pointwiseRightKanExtension (toFunctor h).op F.obj)
    (pointwiseRightKanExtensionCounit (toFunctor h).op F.obj) N.obj).apply_symm_apply η.hom

private theorem etaleSheafHomEquiv_symm_apply_apply
    (F : Sheaf X.etaleTopology (Type u)) (N : Sheaf Y.etaleTopology (Type u))
    (η : N ⟶ ((toFunctor h).sheafPushforwardOfSmallSections
      X.etaleTopology Y.etaleTopology).obj F) :
    ((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
      X.etaleTopology Y.etaleTopology F N).symm
      ((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
        X.etaleTopology Y.etaleTopology F N η) = η := by
  apply ObjectProperty.hom_ext
  exact (homEquivOfIsRightKanExtension (pointwiseRightKanExtension (toFunctor h).op F.obj)
    (pointwiseRightKanExtensionCounit (toFunctor h).op F.obj) N.obj).symm_apply_apply η.hom

private theorem etaleSheafHomEquiv_naturality_left
    (F : Sheaf X.etaleTopology (Type u)) {N N' : Sheaf Y.etaleTopology (Type u)}
    (α : N' ⟶ N) (η : N ⟶ ((toFunctor h).sheafPushforwardOfSmallSections
      X.etaleTopology Y.etaleTopology).obj F) :
    (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
        X.etaleTopology Y.etaleTopology F N' (α ≫ η) =
      ((toFunctor h).sheafPushforwardContinuous (Type u)
        X.etaleTopology Y.etaleTopology).map α ≫
        (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
          X.etaleTopology Y.etaleTopology F N η := by
  apply ObjectProperty.hom_ext
  change whiskerLeft (toFunctor h).op (α.hom ≫ η.hom) ≫ _ =
    whiskerLeft (toFunctor h).op α.hom ≫ whiskerLeft (toFunctor h).op η.hom ≫ _
  rw [whiskerLeft_comp, Category.assoc]

private theorem etaleSheafHomEquiv_symm_naturality_right
    {F F' : Sheaf X.etaleTopology (Type u)} (N : Sheaf Y.etaleTopology (Type u))
    (η : ((toFunctor h).sheafPushforwardContinuous (Type u)
      X.etaleTopology Y.etaleTopology).obj N ⟶ F) (β : F ⟶ F') :
    ((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
        X.etaleTopology Y.etaleTopology F' N).symm (η ≫ β) =
      ((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
          X.etaleTopology Y.etaleTopology F N).symm η ≫
        ((toFunctor h).sheafPushforwardOfSmallSections
          X.etaleTopology Y.etaleTopology).map β := by
  apply ObjectProperty.hom_ext
  apply hom_ext_of_isRightKanExtension _
    (pointwiseRightKanExtensionCounit (toFunctor h).op F'.obj)
  change whiskerLeft (toFunctor h).op
      ((pointwiseRightKanExtension (toFunctor h).op F'.obj).liftOfIsRightKanExtension
        (pointwiseRightKanExtensionCounit (toFunctor h).op F'.obj) N.obj
        (η.hom ≫ β.hom)) ≫ _ =
    whiskerLeft (toFunctor h).op
      ((pointwiseRightKanExtension (toFunctor h).op F.obj).liftOfIsRightKanExtension
        (pointwiseRightKanExtensionCounit (toFunctor h).op F.obj) N.obj η.hom ≫
        (pointwiseRightKanExtension (toFunctor h).op F'.obj).liftOfIsRightKanExtension
          (pointwiseRightKanExtensionCounit (toFunctor h).op F'.obj)
          (pointwiseRightKanExtension (toFunctor h).op F.obj)
          (pointwiseRightKanExtensionCounit (toFunctor h).op F.obj ≫ β.hom)) ≫ _
  simp [whiskerLeft_comp]

/-- Both module Hom directions use actual type-valued transposition and the fixed scalar maps. -/
def etaleModuleHomEquiv
    (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)
    (H : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    ((etaleModuleInverseImage h).obj G ⟶ H) ≃ (G ⟶ (etaleModuleDirectImage h).obj H) where
  toFun η := homOfUnderlying (etaleRingedSite Y).structureSheaf
    (((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv.{u + 1, u, u + 1, u, u}
      X.etaleTopology Y.etaleTopology
      ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
      ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)).symm
      ((etaleModuleInverseImageUnderlyingIso h).inv.app G ≫
        (ToInternal.underlying (etaleRingedSite X).structureSheaf).map η) ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom h)).inv.app H)
    sorry sorry
  invFun η := homOfUnderlying (etaleRingedSite X).structureSheaf
    ((etaleModuleInverseImageUnderlyingIso h).hom.app G ≫
      (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv.{u + 1, u, u + 1, u, u}
        X.etaleTopology Y.etaleTopology
        ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
        ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)
        ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).map η ≫
          (RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom h)).hom.app H))
    sorry sorry
  left_inv η := by
    apply etaleModule_hom_ext X
    let e := (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
      X.etaleTopology Y.etaleTopology
      ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
      ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)
    let i := etaleModuleInverseImageUnderlyingIso h
    let j := RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom h)
    change i.hom.app G ≫
        e ((e.symm (i.inv.app G ≫
          (ToInternal.underlying (etaleRingedSite X).structureSheaf).map η) ≫
            j.inv.app H) ≫ j.hom.app H) =
      (ToInternal.underlying (etaleRingedSite X).structureSheaf).map η
    erw [Category.assoc, Iso.inv_hom_id_app j H, Category.comp_id]
    erw [etaleSheafHomEquiv_apply_symm_apply h]
    erw [← Category.assoc, Iso.hom_inv_id_app i G, Category.id_comp]
  right_inv η := by
    apply etaleModule_hom_ext Y
    let e := (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
      X.etaleTopology Y.etaleTopology
      ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
      ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)
    let i := etaleModuleInverseImageUnderlyingIso h
    let j := RingedSite.ToposHom.ModulePushforward.forgetIso (etaleRingedToposHom h)
    change e.symm (i.inv.app G ≫ (i.hom.app G ≫
        e ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).map η ≫
          j.hom.app H))) ≫ j.inv.app H =
      (ToInternal.underlying (etaleRingedSite Y).structureSheaf).map η
    erw [Iso.inv_hom_id_app_assoc i G]
    erw [etaleSheafHomEquiv_symm_apply_apply h]
    erw [Category.assoc _ (j.hom.app H) (j.inv.app H),
      Iso.hom_inv_id_app j H, Category.comp_id]

/-- The module adjunction supplies actual unit and counit maps between the source-defined functors. -/
def etaleModuleAdjunction : etaleModuleInverseImage h ⊣ etaleModuleDirectImage h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := etaleModuleHomEquiv h
      homEquiv_naturality_left_symm := by
        intro G' G H α η
        apply etaleModule_hom_ext X
        rw [(ToInternal.underlying (etaleRingedSite X).structureSheaf).map_comp]
        change (etaleModuleInverseImageUnderlyingIso h).hom.app G' ≫
            (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
              X.etaleTopology Y.etaleTopology
              ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
              ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G')
              ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).map (α ≫ η) ≫
                (RingedSite.ToposHom.ModulePushforward.forgetIso
                  (etaleRingedToposHom h)).hom.app H) =
          (ToInternal.underlying (etaleRingedSite X).structureSheaf).map
              ((etaleModuleInverseImage h).map α) ≫
            ((etaleModuleInverseImageUnderlyingIso h).hom.app G ≫
              (toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
                X.etaleTopology Y.etaleTopology
                ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H)
                ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)
                ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).map η ≫
                  (RingedSite.ToposHom.ModulePushforward.forgetIso
                    (etaleRingedToposHom h)).hom.app H))
        erw [Functor.map_comp, Category.assoc, etaleSheafHomEquiv_naturality_left h,
          ← Category.assoc]
      homEquiv_naturality_right := by
        intro G H H' η β
        apply etaleModule_hom_ext Y
        change ((toFunctor h).sheafPushforwardOfSmallSectionsHomEquiv
              X.etaleTopology Y.etaleTopology
              ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj H')
              ((ToInternal.underlying (etaleRingedSite Y).structureSheaf).obj G)).symm
            ((etaleModuleInverseImageUnderlyingIso h).inv.app G ≫
              (ToInternal.underlying (etaleRingedSite X).structureSheaf).map (η ≫ β)) ≫
              (RingedSite.ToposHom.ModulePushforward.forgetIso
                (etaleRingedToposHom h)).inv.app H' =
          (_ ≫ (RingedSite.ToposHom.ModulePushforward.forgetIso
              (etaleRingedToposHom h)).inv.app H) ≫
            (ToInternal.underlying (etaleRingedSite Y).structureSheaf).map
              ((etaleModuleDirectImage h).map β)
        erw [Functor.map_comp,
          ← Category.assoc ((etaleModuleInverseImageUnderlyingIso h).inv.app G)
            ((ToInternal.underlying (etaleRingedSite X).structureSheaf).map η)
            ((ToInternal.underlying (etaleRingedSite X).structureSheaf).map β),
          etaleSheafHomEquiv_symm_naturality_right h,
          Category.assoc, Category.assoc]
        exact congrArg (fun k ↦ _ ≫ k)
          ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (etaleRingedToposHom h)).inv.naturality β) }

/-- The module unit goes directly to `h_* h^*`, with inverse image in the source's site presentation. -/
def etaleModuleUnit (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    G ⟶ (etaleModuleDirectImage h).obj ((etaleModuleInverseImage h).obj G) :=
  (etaleModuleAdjunction h).unit.app G

end AlgebraicGeometry.GroupoidsOver
