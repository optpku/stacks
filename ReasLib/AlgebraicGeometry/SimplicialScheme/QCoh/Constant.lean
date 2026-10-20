/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Basic
public import ReasLib.AlgebraicGeometry.SimplicialScheme.CechNerve
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Constant extension of quasi-coherent modules
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject CategoryTheory.ObjectProperty Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The identity map on structure-sheaf sections at a diagram open of a constant scheme. -/
def constStructureSheafMap_app (S : Scheme.{u})
    (W : (zariskiSite (forgetToTop.obj (constScheme S)))ᵒᵖ) :
    (structureSheaf (constScheme S)).obj.obj W ⟶
      S.ringCatSheaf.obj.obj ((constProjection S.toTopCat).op.obj W) :=
  𝟙 _

/-- Identity maps on sections commute with restrictions after forgetting the simplex degree. -/
theorem constStructureSheafMap_naturality (S : Scheme.{u})
    {W Z : (zariskiSite (forgetToTop.obj (constScheme S)))ᵒᵖ} (η : W ⟶ Z) :
    (structureSheaf (constScheme S)).obj.map η ≫ constStructureSheafMap_app S Z =
      constStructureSheafMap_app S W ≫
        S.ringCatSheaf.obj.map ((constProjection S.toTopCat).op.map η) :=
  sorry

/-- The structure-sheaf map for the degree-forgetting projection of a constant scheme. -/
def constStructureSheafMap (S : Scheme.{u}) :
    structureSheaf (constScheme S) ⟶
      ((constProjection S.toTopCat).sheafPushforwardContinuous RingCat.{u}
        (zariskiTopology (constSpace S.toTopCat))
        (Opens.grothendieckTopology S.toTopCat)).obj S.ringCatSheaf :=
  ⟨{ app := constStructureSheafMap_app S
     naturality := fun _ _ η ↦ constStructureSheafMap_naturality S η }⟩

/-- Degreewise constant extension of module sheaves from a scheme to its constant
simplicial scheme. -/
def constModulePullback (S : Scheme.{u}) :
    S.Modules ⥤ SheafOfModules.{u} (structureSheaf (constScheme S)) where
  obj M := (SheafOfModules.pushforward
    (J := zariskiTopology (constSpace S.toTopCat)) (constStructureSheafMap S)).obj M
  map f := (SheafOfModules.pushforward
    (J := zariskiTopology (constSpace S.toTopCat)) (constStructureSheafMap S)).map f
  map_id M := (SheafOfModules.pushforward
    (J := zariskiTopology (constSpace S.toTopCat)) (constStructureSheafMap S)).map_id M
  map_comp f g := (SheafOfModules.pushforward
    (J := zariskiTopology (constSpace S.toTopCat)) (constStructureSheafMap S)).map_comp f g

/-- The additive presheaf of constant extension is precomposition with the
degree-forgetting projection. -/
theorem constModulePullback_obj_presheaf (S : Scheme.{u}) (M : S.Modules) :
    ((constModulePullback S).obj M).val.presheaf =
      (constProjection S.toTopCat).op ⋙ M.val.presheaf := rfl

/-- Degreewise constant extension preserves quasi-coherence. -/
theorem constPullback_le_inverseImage (S : Scheme.{u}) :
    Scheme.quasiCoherentModuleProperty S ≤
      (quasiCoherentModuleProperty (constScheme S)).inverseImage
        (constModulePullback S) :=
  sorry

/-- Degreewise constant extension restricted to quasi-coherent modules. -/
def QCoh.constPullback (S : Scheme.{u}) :
    Scheme.QCoh S ⥤ QCoh (constScheme S) :=
  FullSubcategory.restrict (constModulePullback S) (constPullback_le_inverseImage S)

end AlgebraicGeometry.SimplicialObject
