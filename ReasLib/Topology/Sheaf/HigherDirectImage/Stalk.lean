/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaf.Cohomology.SpecializingPreimage
public import ReasLib.Topology.Sheaf.HigherDirectImage.Presheaf
public import ReasLib.Topology.Sheaves.Stalks.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of higher direct images

The stalk of a higher direct image is canonically the colimit of the cohomology presheaf over
open neighbourhoods. Composing this identification with the specializing-preimage comparison
gives the canonical map in Lemma 20.22.2.

Neither comparison map requires spectral hypotheses. Spectrality enters only in the theorem that
the final comparison is an isomorphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open TopCat.Sheaf.Cohomology

noncomputable section

universe u

namespace TopCat.Sheaf.HigherDirectImage.Stalk

variable {X Y : TopCat.{u}}

/-- Sheafification identifies the neighbourhood-cohomology colimit with the stalk of the
sheafified cohomology presheaf. -/
@[stacks 0A3E "neighbourhood cohomology after sheafification"]
noncomputable def sheafificationIso (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (SpecializingPreimage.diagram f y F p) ≅
      ((Presheaf.sheafifiedCohomologyFunctor f p).obj F).presheaf.stalk y :=
  TopCat.Presheaf.SheafificationStalk.iso
    ((Presheaf.cohomologyFunctor f p).obj F) y

/-- The sheafified cohomology-presheaf comparison identifies its stalk with the stalk of the
higher direct image. -/
@[stacks 0A3E "sheafified cohomology comparison on a stalk"]
noncomputable def higherDirectImageIso (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    ((Presheaf.sheafifiedCohomologyFunctor f p).obj F).presheaf.stalk y ≅
      (higherDirectImage f F p).presheaf.stalk y :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).mapIso
      (Presheaf.objIso f F p))

/-- The canonical identification of the neighbourhood-cohomology colimit with the stalk of the
higher direct image. -/
@[stacks 0A3E "neighbourhood cohomology as a higher-direct-image stalk"]
noncomputable def cohomologyIso (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (SpecializingPreimage.diagram f y F p) ≅
      (higherDirectImage f F p).presheaf.stalk y :=
  sheafificationIso f y F p ≪≫ higherDirectImageIso f y F p

/-- The canonical map from a neighbourhood-cohomology stage to the stalk of the higher direct
image. -/
@[stacks 0A3E "neighbourhood stage map to a higher-direct-image stalk"]
noncomputable def stageMap (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : OpenNhds y) :
    (SpecializingPreimage.diagram f y F p).obj (Opposite.op U) ⟶
      (higherDirectImage f F p).presheaf.stalk y :=
  colimit.ι (SpecializingPreimage.diagram f y F p) (Opposite.op U) ≫
    (cohomologyIso f y F p).hom

/-- The map on neighbourhood-cohomology colimits induced by a morphism of coefficient sheaves. -/
@[stacks 0A3E "coefficient map on neighbourhood-cohomology colimits"]
abbrev colimitMap (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    colimit (SpecializingPreimage.diagram f y F p) ⟶
      colimit (SpecializingPreimage.diagram f y G p) :=
  colim.map (SpecializingPreimage.diagramMap f y a p)

/-- The map on higher-direct-image stalks induced by a morphism of coefficient sheaves. -/
@[stacks 0A3E "coefficient map on higher-direct-image stalks"]
abbrev stalkMap (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    (higherDirectImage f F p).presheaf.stalk y ⟶
      (higherDirectImage f G p).presheaf.stalk y :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
      (higherDirectImageMap f a p))

/-- The neighbourhood-colimit identification with the higher-direct-image stalk is natural in
the coefficient sheaf. -/
@[stacks 0A3E "coefficient naturality of the higher-direct-image stalk identification"]
theorem cohomologyIso_hom_naturality (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    colimitMap f y a p ≫ (cohomologyIso f y G p).hom =
      (cohomologyIso f y F p).hom ≫ stalkMap f y a p := sorry

/-- Taking stalks after sheafification gives the natural identification between neighbourhood
cohomology and higher-direct-image stalks. -/
@[stacks 0A3E "cohomology-presheaf comparison on a stalk"]
noncomputable def cohomologyNatIso (f : X ⟶ Y) (y : Y) (p : ℕ) :
    Presheaf.cohomologyFunctor f p ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y ≅
      TopCat.Sheaf.higherDirectImageFunctor f p ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) :=
  NatIso.ofComponents (fun F => cohomologyIso f y F p)
    (fun a => cohomologyIso_hom_naturality f y a p)

/-- The canonical map from a neighbourhood stage to the higher-direct-image stalk is natural in
the coefficient sheaf. -/
@[reassoc, stacks 0A3E "coefficient naturality of higher-direct-image stalk stage maps"]
theorem stageMap_map (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) (U : OpenNhds y) :
    (SpecializingPreimage.diagramMap f y a p).app (Opposite.op U) ≫
        stageMap f y G p U =
      stageMap f y F p U ≫ stalkMap f y a p := sorry

/-- The canonical comparison from a higher-direct-image stalk to cohomology on the inverse image
of the point's specializing locus. -/
@[stacks 0A3E "higher-direct-image stalk comparison"]
noncomputable def comparison (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (higherDirectImage f F p).presheaf.stalk y ⟶
      SpecializingPreimage.target f y F p :=
  (cohomologyIso f y F p).inv ≫
    SpecializingPreimage.comparison f y F p

/-- On every neighbourhood, the stalk comparison agrees with the canonical pullback map to
specializing-locus cohomology. -/
@[reassoc, stacks 0A3E "higher-direct-image stalk comparison at a neighbourhood"]
theorem stageMap_comp_comparison (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : OpenNhds y) :
    stageMap f y F p U ≫ comparison f y F p =
      SpecializingPreimage.stageMap f y F p U := sorry

/-- The higher-direct-image stalk comparison is natural in the coefficient sheaf. -/
@[stacks 0A3E "coefficient naturality of the higher-direct-image stalk comparison"]
theorem comparison_map (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    stalkMap f y a p ≫ comparison f y G p =
      comparison f y F p ≫ SpecializingPreimage.targetMap f y a p := sorry

/-- Lemma 20.22.2 (0A3E): for a spectral map from a spectral space to a prespectral space, the
canonical map from the stalk of the higher direct image to cohomology on the inverse image of the
point's specializing locus is an isomorphism. -/
@[stacks 0A3E "stalk of a higher direct image"]
theorem comparison_isIso [SpectralSpace X] [PrespectralSpace Y]
    (f : X ⟶ Y) (hf : IsSpectralMap f) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison f y F p) := sorry

end TopCat.Sheaf.HigherDirectImage.Stalk

/- Audit the explicit comparison data. -/
