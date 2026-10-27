/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Coefficient isomorphisms for module presheaves -/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace PresheafOfModules.Restriction

variable {C : Type u'} [Category.{v'} C]
variable {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- Transport to isomorphic coefficients and back is naturally isomorphic to the identity. -/
def isoUnit (e : R ≅ R') :
    𝟭 (PresheafOfModules.{v} R) ≅
      restrictScalars e.inv ⋙ restrictScalars e.hom :=
  idIso R ≪≫ (compIso' e.hom e.inv (𝟙 R) e.hom_inv_id.symm).symm

/-- Transport back from isomorphic coefficients and forward recovers the original module. -/
def isoCounit (e : R ≅ R') :
    restrictScalars e.hom ⋙ restrictScalars e.inv ≅
      𝟭 (PresheafOfModules.{v} R') :=
  compIso' e.inv e.hom (𝟙 R') e.inv_hom_id.symm ≪≫ (idIso R').symm

/-- Isomorphic ring presheaves have equivalent categories of module presheaves. -/
def equivalenceOfIso (e : R ≅ R') :
    PresheafOfModules.{v} R ≌ PresheafOfModules.{v} R' :=
  CategoryTheory.Equivalence.mk (restrictScalars e.inv) (restrictScalars e.hom)
    (isoUnit e) (isoCounit e)

/-- Identity-site pushforward along invertible coefficients admits a left adjoint. -/
instance pushforwardOverIdIsRightAdjointOfIsIso (α : R ⟶ R') [IsIso α] :
    (pushforward.{v} (F := 𝟭 C) α).IsRightAdjoint :=
  (equivalenceOfIso.{v} (asIso α)).toAdjunction.isRightAdjoint

end PresheafOfModules.Restriction
