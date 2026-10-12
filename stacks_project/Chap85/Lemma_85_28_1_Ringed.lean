/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import stacks_project.Chap85.Lemma_85_2_1_Site

/-!
# Zariski ringed site of a simplicial scheme

The identity-degree Zariski site of the underlying simplicial space of a simplicial scheme,
equipped with the sheaf of rings assembled from the stagewise structure sheaves.
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

/-- The structure presheaf of rings on the Zariski site of a simplicial scheme, with value
on a diagram open `W` equal to the structure sheaf of `U.obj W.base` on `W.opens`. -/
def structurePresheaf (U : SimplicialObject Scheme.{u}) :
    (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ RingCat.{u} where
  obj W := (U.obj W.unop.base).ringCatSheaf.obj.obj (op W.unop.opens)
  map η := structurePresheafMap η
  map_id := sorry
  map_comp := sorry

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

/-- The Zariski ringed site `U_Zar` of a simplicial scheme. -/
abbrev zariskiRingedSite (U : SimplicialObject Scheme.{u}) : RingedSite :=
  RingedSite.ofRingSheaf (zariskiTopology (forgetToTop.obj U)) (structureSheaf U)

/-- The structure sheaf of `zariskiRingedSite U` is `structureSheaf U`. -/
theorem zariskiRingedSite_structureSheaf (U : SimplicialObject Scheme.{u}) :
    (zariskiRingedSite U).structureSheaf = structureSheaf U :=
  rfl

end AlgebraicGeometry.SimplicialObject
