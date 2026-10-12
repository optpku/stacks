/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Modules
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An open subscheme of an étale chart is again an étale chart of the same algebraic space. -/
theorem openChart_obj_isEtale (U : site X) (subset : U.left.left.Opens) :
    Representable.Etale (yoneda.map (Over.homMk subset.ι rfl :
      (U.left.left.restrictFunctor ⋙ Over.map U.left.hom).obj subset ⟶ U.left) ≫ U.hom) := sorry

/-- Inclusion of open subschemes commutes with their structural maps to the algebraic space. -/
theorem openChart_map_w (U : site X) {source target : U.left.left.Opens}
    (map : source ⟶ target) :
    let schemes := U.left.left.restrictFunctor ⋙ Over.map U.left.hom
    yoneda.map (schemes.map map) ≫
        (yoneda.map (Over.homMk target.ι rfl : schemes.obj target ⟶ U.left) ≫ U.hom) =
      yoneda.map (Over.homMk source.ι rfl : schemes.obj source ⟶ U.left) ≫ U.hom := sorry

/-- Sending an open subscheme to its étale chart preserves identity morphisms. -/
theorem openChart_map_id (U : site X) (subset : U.left.left.Opens) :
    let schemes := U.left.left.restrictFunctor ⋙ Over.map U.left.hom
    let chart : site X := MorphismProperty.CostructuredArrow.mk ⊤
      (yoneda.map (Over.homMk subset.ι rfl : schemes.obj subset ⟶ U.left) ≫ U.hom)
      (openChart_obj_isEtale U subset)
    (MorphismProperty.CostructuredArrow.homMk (schemes.map (𝟙 subset)) trivial
      (openChart_map_w U (𝟙 subset)) : chart ⟶ chart) = 𝟙 chart := sorry

/-- Sending open subschemes to their étale charts preserves composition. -/
theorem openChart_map_comp (U : site X) {source middle target : U.left.left.Opens}
    (map : source ⟶ middle) (next : middle ⟶ target) :
    let schemes := U.left.left.restrictFunctor ⋙ Over.map U.left.hom
    let sourceChart : site X := MorphismProperty.CostructuredArrow.mk ⊤
      (yoneda.map (Over.homMk source.ι rfl : schemes.obj source ⟶ U.left) ≫ U.hom)
      (openChart_obj_isEtale U source)
    let middleChart : site X := MorphismProperty.CostructuredArrow.mk ⊤
      (yoneda.map (Over.homMk middle.ι rfl : schemes.obj middle ⟶ U.left) ≫ U.hom)
      (openChart_obj_isEtale U middle)
    let targetChart : site X := MorphismProperty.CostructuredArrow.mk ⊤
      (yoneda.map (Over.homMk target.ι rfl : schemes.obj target ⟶ U.left) ≫ U.hom)
      (openChart_obj_isEtale U target)
    (MorphismProperty.CostructuredArrow.homMk (schemes.map (map ≫ next)) trivial
      (openChart_map_w U (map ≫ next)) : sourceChart ⟶ targetChart) =
      (MorphismProperty.CostructuredArrow.homMk (schemes.map map) trivial
        (openChart_map_w U map) : sourceChart ⟶ middleChart) ≫
      (MorphismProperty.CostructuredArrow.homMk (schemes.map next) trivial
        (openChart_map_w U next) : middleChart ⟶ targetChart) := sorry

/-- The open-chart functor sends a Zariski open of an étale chart to its composite chart
over the algebraic space. -/
def openChart (U : site X) : U.left.left.Opens ⥤ site X where
  obj subset := MorphismProperty.CostructuredArrow.mk ⊤
    (yoneda.map (Over.homMk subset.ι rfl :
      (U.left.left.restrictFunctor ⋙ Over.map U.left.hom).obj subset ⟶ U.left) ≫ U.hom)
    (openChart_obj_isEtale U subset)
  map map := MorphismProperty.CostructuredArrow.homMk
    ((U.left.left.restrictFunctor ⋙ Over.map U.left.hom).map map) trivial
    (openChart_map_w U map)
  map_id := openChart_map_id U
  map_comp := openChart_map_comp U

/-- The functor from the Zariski opens of an étale chart to the small étale site is
continuous. -/
instance openChart_isContinuous (U : site X) :
    Functor.IsContinuous (openChart U)
      (Opens.grothendieckTopology U.left.left) (topology X) := sorry

/-- The comparison between sections on an open and global sections on its open subscheme
is natural in the open. -/
theorem openChartStructureMap_naturality (U : site X)
    {source target : U.left.left.Opensᵒᵖ} (map : source ⟶ target) :
    U.left.left.ringCatSheaf.obj.map map ≫
        (forget₂ CommRingCat RingCat).map
          ((Scheme.restrictFunctorΓ (X := U.left.left)).inv.app target) =
      (forget₂ CommRingCat RingCat).map
          ((Scheme.restrictFunctorΓ (X := U.left.left)).inv.app source) ≫
        (structurePresheaf X).map ((openChart U).op.map map) := sorry

/-- The structure-sheaf comparison on a chart identifies sections on an open with global
sections of its open subscheme. -/
def openChartStructureMap (U : site X) :
    U.left.left.ringCatSheaf ⟶
      ((openChart U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology U.left.left) (topology X)).obj
          (structureSheaf X) :=
  ⟨{ app := fun subset => (forget₂ CommRingCat RingCat).map
       ((Scheme.restrictFunctorΓ (X := U.left.left)).inv.app subset)
     naturality := fun _ _ map => openChartStructureMap_naturality U map }⟩

/-- Realize a small étale module sheaf as the Zariski module on an étale scheme chart. -/
def Modules.toScheme (U : site X) : Modules X ⥤ U.left.left.Modules :=
  SheafOfModules.pushforward (openChartStructureMap U)

/-- The underlying abelian presheaf on a chart is obtained by evaluating the étale module
on the composite charts of its Zariski opens. -/
theorem Modules.toScheme_apply (U : site X) (F : Modules X) :
    ((Modules.toScheme U).obj F).val.presheaf = (openChart U).op ⋙ F.val.presheaf := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
