/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site

/-!
# The structure sheaf on the simplicial Zariski site

The structure sheaves of the stages assemble into a ring sheaf on the
identity-stage open-cover site of a simplicial scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject Opposite AlgebraicGeometry
open TopologicalSpace TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The underlying simplicial space of a simplicial scheme. -/
abbrev forgetToTop : SimplicialObject Scheme.{u} ⥤ SimplicialObject TopCat.{u} :=
  (SimplicialObject.whiskering Scheme TopCat).obj Scheme.forgetToTop

/-- On objects, `forgetToTop` is postcomposition with `Scheme.forgetToTop`. -/
theorem forgetToTop_obj (U : SimplicialObject Scheme.{u}) :
    forgetToTop.obj U = U ⋙ Scheme.forgetToTop :=
  rfl

/-- Components of `forgetToTop.map f` are the underlying maps of the components of `f`. -/
theorem forgetToTop_map_app {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (n : SimplexCategoryᵒᵖ) :
    (forgetToTop.map f).app n = Scheme.forgetToTop.map (f.app n) :=
  rfl

/-- Restriction of the structure presheaf of a simplicial scheme along a morphism of
diagram opens, assembled from the stagewise map `toRingCatSheafHom`. -/
def structurePresheafMap {U : SimplicialObject Scheme.{u}}
    {W Z : (zariskiSite (forgetToTop.obj U))ᵒᵖ} (η : W ⟶ Z) :
    (U.obj W.unop.base).ringCatSheaf.obj.obj (op W.unop.opens) ⟶
      (U.obj Z.unop.base).ringCatSheaf.obj.obj (op Z.unop.opens) :=
  (U.map η.unop.base).toRingCatSheafHom.hom.app (op W.unop.opens) ≫
    (U.obj Z.unop.base).ringCatSheaf.obj.map
      (homOfLE (fun _ hx ↦ η.unop.mapsTo hx)).op

/-- Restriction along the identity of a diagram open is the identity on sections. -/
theorem structurePresheafMap_id (U : SimplicialObject Scheme.{u})
    (W : (zariskiSite (forgetToTop.obj U))ᵒᵖ) :
    structurePresheafMap (𝟙 W) = 𝟙 _ := sorry

/-- Restriction along a composite of diagram-open arrows is the composite restriction. -/
theorem structurePresheafMap_comp (U : SimplicialObject Scheme.{u})
    {W Z T : (zariskiSite (forgetToTop.obj U))ᵒᵖ} (η : W ⟶ Z) (θ : Z ⟶ T) :
    structurePresheafMap (η ≫ θ) = structurePresheafMap η ≫ structurePresheafMap θ := sorry

/-- The structure presheaf of rings on the Zariski site of a simplicial scheme, with value
on a diagram open `W` equal to the structure sheaf of `U.obj W.base` on `W.opens`. -/
def structurePresheaf (U : SimplicialObject Scheme.{u}) :
    (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ RingCat.{u} where
  obj W := (U.obj W.unop.base).ringCatSheaf.obj.obj (op W.unop.opens)
  map η := structurePresheafMap η
  map_id := structurePresheafMap_id U
  map_comp := structurePresheafMap_comp U

/-- The structure presheaf of a simplicial scheme is a sheaf for the identity-degree Zariski
topology. -/
theorem structurePresheaf_isSheaf (U : SimplicialObject Scheme.{u}) :
    Presheaf.IsSheaf (zariskiTopology (forgetToTop.obj U)) (structurePresheaf U) :=
  sorry

/-- The structure sheaf of rings on the Zariski site of a simplicial scheme. -/
def structureSheaf (U : SimplicialObject Scheme.{u}) :
    Sheaf (zariskiTopology (forgetToTop.obj U)) RingCat.{u} :=
  ⟨structurePresheaf U, structurePresheaf_isSheaf U⟩

/-- On `DiagramOpens.ofOpens n W`, the structure sheaf of a simplicial scheme is the ordinary
structure sheaf of the stage `U.obj n` on `W`. -/
theorem structureSheaf_obj (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)
    (W : Opens ((forgetToTop.obj U).obj n)) :
    (structureSheaf U).obj.obj (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W)) =
      (U.obj n).ringCatSheaf.obj.obj (op W) :=
  rfl

end AlgebraicGeometry.SimplicialObject
