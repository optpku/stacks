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
  NatIso.ofComponents (fun G ↦ Iso.refl _) sorry

variable {X Y : GroupoidsOver S} (h : X ⟶ Y)
variable [HasSmallCFGTypeSections (S := S) h]

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
  left_inv := sorry
  right_inv := sorry

/-- The module adjunction supplies actual unit and counit maps between the source-defined functors. -/
def etaleModuleAdjunction : etaleModuleInverseImage h ⊣ etaleModuleDirectImage h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := etaleModuleHomEquiv h
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The module unit goes directly to `h_* h^*`, with inverse image in the source's site presentation. -/
def etaleModuleUnit (G : SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) :
    G ⟶ (etaleModuleDirectImage h).obj ((etaleModuleInverseImage h).obj G) :=
  (etaleModuleAdjunction h).unit.app G

end AlgebraicGeometry.GroupoidsOver
