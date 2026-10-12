/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import stacks_project.Chap85.Lemma_85_28_4_QCoh

/-!
# Stage restriction of quasi-coherent modules on `U_Zar`

The category of quasi-coherent modules on the Zariski ringed site of a simplicial scheme is
`SimplicialObject.QCoh` from Lemma 85.28.4. This module adds the smart constructor and the
restriction of an `O_{U_Zar}`-module to a single stage `U.obj n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite AlgebraicGeometry
open TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

namespace QCoh

/-- Package a quasi-coherent module sheaf on `U_Zar` as an object of `QCoh U`. -/
def of {U : SimplicialObject Scheme.{u}}
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf)
    [F.IsQuasicoherent] : QCoh U :=
  ⟨F, inferInstance⟩

/-- The underlying module sheaf of `QCoh.of F` is `F`. -/
theorem of_obj {U : SimplicialObject Scheme.{u}}
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf)
    [F.IsQuasicoherent] :
    (of F).obj = F :=
  sorry

/-- The inclusion of `QCoh U` forgets quasi-coherence and returns the underlying module sheaf. -/
theorem inclusion_obj (U : SimplicialObject Scheme.{u}) (F : QCoh U) :
    (inclusion U).obj F = F.obj :=
  sorry

end QCoh

/-- The identity-stage diagram-open morphism associated to an inclusion of opens of `U.obj n`. -/
def moduleComponentHom {U : SimplicialObject Scheme.{u}} {n : SimplexCategoryᵒᵖ}
    {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (f : W ⟶ Z) :
    DiagramOpens.ofOpens (forgetToTop.obj U) n Z.unop ⟶
      DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop :=
  DiagramOpens.homOfLE (leOfHom f.unop)

/-- The structure-sheaf restriction along `moduleComponentHom f` is the ordinary restriction
on the stage `U.obj n`. -/
theorem moduleComponentHom_structureMap {U : SimplicialObject Scheme.{u}}
    {n : SimplexCategoryᵒᵖ} {W Z : (Opens ((forgetToTop.obj U).obj n))ᵒᵖ} (f : W ⟶ Z) :
    ((zariskiRingedSite U).structureSheaf.obj.map (moduleComponentHom f).op).hom =
      ((U.obj n).ringCatSheaf.obj.map f).hom :=
  sorry

/-- Underlying presheaf of the restriction of an `O_{U_Zar}`-module to the stage `U.obj n`. -/
def moduleComponentPresheaf (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf) :
    PresheafOfModules.{u} (U.obj n).ringCatSheaf.obj where
  obj W := F.val.obj (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop))
  map {W Z} f :=
    F.val.map (moduleComponentHom f).op ≫
      (ModuleCat.restrictScalarsCongr (moduleComponentHom_structureMap f)).hom.app _
  map_id := sorry
  map_comp := sorry

/-- Restriction of an `O_{U_Zar}`-module to the ordinary module sheaf on the stage `U.obj n`. -/
def moduleComponent (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.{u} (zariskiRingedSite U).structureSheaf ⥤ (U.obj n).Modules where
  obj F := ⟨moduleComponentPresheaf U n F, sorry⟩
  map {F G} f :=
    ⟨{ app := fun W ↦ f.val.app (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W.unop))
       naturality := sorry }⟩
  map_id := sorry
  map_comp := sorry

/-- On an open `W` of the stage `U.obj n`, `moduleComponent` evaluates the sheaf on the
corresponding diagram open. -/
theorem moduleComponent_obj (U : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ)
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf)
    (W : Opens ((forgetToTop.obj U).obj n)) :
    ((moduleComponent U n).obj F).val.obj (op W) =
      F.val.obj (op (DiagramOpens.ofOpens (forgetToTop.obj U) n W)) :=
  sorry

/-- Restriction of a quasi-coherent module on `U_Zar` to any stage remains quasi-coherent. -/
instance moduleComponent_isQuasicoherent (U : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ)
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf)
    [F.IsQuasicoherent] :
    ((moduleComponent U n).obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.SimplicialObject
