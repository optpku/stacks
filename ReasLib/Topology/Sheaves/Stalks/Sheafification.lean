/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Skyscraper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of sheafifications

This file is the topological-space, explicit-inverse refinement of the general site-point fact that
sheafification preserves fibers. The inverse is constructed through the
sheafification--skyscraper and stalk--skyscraper Hom equivalences, rather than selected from an
`IsIso` proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u v

namespace TopCat.Presheaf.SheafificationStalk

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
variable [HasTerminal C] [HasColimits C]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- The sheafification-to-skyscraper mate used to construct the explicit inverse on stalks. -/
@[stacks 007Z "sheafification-to-skyscraper comparison"]
noncomputable def toSkyscraper (F : X.Presheaf C) (x : X) :
    (presheafToSheaf (Opens.grothendieckTopology X) C).obj F ⟶
      TopCat.Sheaf.Skyscraper.atPoint x (F.stalk x) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) C).homEquiv F
      (TopCat.Sheaf.Skyscraper.atPoint x (F.stalk x))).symm
    ((TopCat.Sheaf.Skyscraper.presheafStalkAdjunction x).unit.app F)

/-- The sheafification-to-skyscraper mate extends the canonical presheaf-to-skyscraper map. -/
private theorem toSkyscraper_unit (F : X.Presheaf C) (x : X) :
    toSheafify (Opens.grothendieckTopology X) F ≫ (toSkyscraper F x).hom =
      (TopCat.Sheaf.Skyscraper.presheafStalkAdjunction x).unit.app F := sorry

/-- The canonical map from a presheaf stalk to the stalk of its sheafification. -/
@[stacks 007Z "sheafification stalk comparison"]
noncomputable abbrev comparison (F : X.Presheaf C) (x : X) :
    F.stalk x ⟶
      (stalkFunctor C x).obj (sheafify (Opens.grothendieckTopology X) F) :=
  (stalkFunctor C x).map (toSheafify (Opens.grothendieckTopology X) F)

/-- The sheafification-stalk comparison sends a germ to the germ of its image under the
sheafification unit. -/
@[reassoc, stacks 007Z "sheafification stalk comparison on germs"]
theorem germ_comparison (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    F.germ U x hx ≫ comparison F x =
      (toSheafify (Opens.grothendieckTopology X) F).app (op U) ≫
        TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) F) U x hx := sorry

/-- The explicit inverse from the stalk of the sheafification of `F` to the stalk of `F`. -/
@[stacks 007Z "inverse sheafification stalk comparison"]
noncomputable def comparisonInv (F : X.Presheaf C) (x : X) :
    (stalkFunctor C x).obj (sheafify (Opens.grothendieckTopology X) F) ⟶ F.stalk x :=
  ((TopCat.Sheaf.Skyscraper.stalkAdjunction x).homEquiv
      ((presheafToSheaf (Opens.grothendieckTopology X) C).obj F) (F.stalk x)).symm
    (toSkyscraper F x)

/-- The inverse comparison sends the germ of a sheafification-unit image back to the original
germ. -/
@[reassoc, stacks 007Z "inverse sheafification stalk comparison on germs"]
theorem toSheafify_germ_comparisonInv
    (F : X.Presheaf C) (U : Opens X) (x : X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology X) F).app (op U) ≫
        TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) F) U x hx ≫
          comparisonInv F x =
      F.germ U x hx := sorry

/-- The sheafification-stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 007Z "sheafification stalk comparison forward-inverse law"]
theorem comparison_hom_inv_id (F : X.Presheaf C) (x : X) :
    comparison F x ≫ comparisonInv F x = 𝟙 _ := sorry

/-- The explicit inverse followed by the sheafification-stalk comparison is the identity. -/
@[simp, stacks 007Z "sheafification stalk comparison inverse-forward law"]
theorem comparison_inv_hom_id (F : X.Presheaf C) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 _ := sorry

/-- Sheafification preserves stalks, with both directions explicitly owned. -/
@[stacks 007Z "sheafification preserves stalks for arbitrary coefficient categories"]
noncomputable def iso (F : X.Presheaf C) (x : X) :
    F.stalk x ≅
      (stalkFunctor C x).obj (sheafify (Opens.grothendieckTopology X) F) where
  hom := comparison F x
  inv := comparisonInv F x
  hom_inv_id := comparison_hom_inv_id F x
  inv_hom_id := comparison_inv_hom_id F x

/-- The sheafification-stalk comparison is available to typeclass search as an isomorphism.
The proof is mathlib's argument for `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`
(the stalk functor and the sheafification adjunction compose to the skyscraper adjunction);
that module is not imported here because its Type-valued `TopCat.Presheaf.sheafify` and
`TopCat.Presheaf.toSheafify` would shadow the site-level names used in this namespace. -/
@[stacks 007Z "sheafification stalk comparison is an isomorphism", instance]
noncomputable instance comparison_isIso (F : X.Presheaf C) (x : X) :
    IsIso (comparison F x) := by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) C)
    (skyscraperSheafForgetAdjunction x)

/-- The forward map of `iso` is the sheafification-unit comparison. -/
@[simp, stacks 007Z "sheafification stalk isomorphism hom"]
theorem iso_hom (F : X.Presheaf C) (x : X) :
    (iso F x).hom = comparison F x := sorry

/-- The inverse map of `iso` is the explicit stalk inverse. -/
@[simp, stacks 007Z "sheafification stalk isomorphism inverse"]
theorem iso_inv (F : X.Presheaf C) (x : X) :
    (iso F x).inv = comparisonInv F x := sorry

/-- The sheafification-stalk comparison is natural in the presheaf. -/
@[reassoc, stacks 007Z "sheafification stalk comparison naturality"]
theorem comparison_naturality
    {F G : X.Presheaf C} (f : F ⟶ G) (x : X) :
    (stalkFunctor C x).map f ≫ comparison G x =
      comparison F x ≫
        (stalkFunctor C x).map
          (sheafifyMap (Opens.grothendieckTopology X) f) := sorry

/-- The explicit inverse sheafification-stalk comparison is natural in the presheaf. -/
@[reassoc, stacks 007Z "inverse sheafification stalk comparison naturality"]
theorem comparisonInv_naturality
    {F G : X.Presheaf C} (f : F ⟶ G) (x : X) :
    (stalkFunctor C x).map
          (sheafifyMap (Opens.grothendieckTopology X) f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ (stalkFunctor C x).map f := sorry

/-- The sheafification-stalk comparisons form a natural transformation in the presheaf. -/
@[stacks 007Z "sheafification stalk comparison natural transformation"]
noncomputable def natTrans (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    stalkFunctor C x ⟶
      sheafification (Opens.grothendieckTopology X) C ⋙ stalkFunctor C x where
  app F := comparison F x
  naturality _ _ f := comparison_naturality f x

/-- A component of `natTrans` is the canonical sheafification-stalk comparison. -/
@[simp, stacks 007Z "sheafification stalk comparison natural transformation component"]
theorem natTrans_app (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    (natTrans C x).app F = comparison F x := sorry

/-- The named inverse comparisons form a natural transformation in the presheaf. -/
@[stacks 007Z "inverse sheafification stalk natural transformation"]
noncomputable def natTransInv (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    sheafification (Opens.grothendieckTopology X) C ⋙ stalkFunctor C x ⟶
      stalkFunctor C x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- A component of `natTransInv` is the explicit inverse sheafification-stalk comparison. -/
@[simp, stacks 007Z "inverse sheafification stalk natural transformation component"]
theorem natTransInv_app (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    (natTransInv C x).app F = comparisonInv F x := sorry

/-- The forward and inverse sheafification-stalk transformations compose to the identity. -/
@[simp, stacks 007Z "sheafification stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    natTrans C x ≫ natTransInv C x = 𝟙 _ := sorry

/-- The inverse and forward sheafification-stalk transformations compose to the identity. -/
@[simp, stacks 007Z "sheafification stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    natTransInv C x ≫ natTrans C x = 𝟙 _ := sorry

/-- Taking a stalk before or after sheafification gives naturally isomorphic functors. -/
@[stacks 007Z "sheafification stalk natural isomorphism"]
noncomputable def natIso (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    stalkFunctor C x ≅
      sheafification (Opens.grothendieckTopology X) C ⋙ stalkFunctor C x :=
  { hom := natTrans C x
    inv := natTransInv C x
    hom_inv_id := natTrans_hom_inv_id C x
    inv_hom_id := natTrans_inv_hom_id C x }

/-- The forward natural transformation of `natIso` is the named comparison transformation. -/
@[simp, stacks 007Z "sheafification stalk natural isomorphism hom"]
theorem natIso_hom (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    (natIso C x).hom = natTrans C x := sorry

/-- The inverse natural transformation of `natIso` is the named inverse transformation. -/
@[simp, stacks 007Z "sheafification stalk natural isomorphism inverse"]
theorem natIso_inv (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (x : X) :
    (natIso C x).inv = natTransInv C x := sorry

/-- A component of `natIso` is the objectwise sheafification-stalk isomorphism. -/
@[simp, stacks 007Z "sheafification stalk natural isomorphism component"]
theorem natIso_app (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    (natIso C x).app F = iso F x := sorry

/-- Forward components of `natIso` are the sheafification-stalk comparisons. -/
@[simp, stacks 007Z "sheafification stalk natural isomorphism hom component"]
theorem natIso_hom_app (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    (natIso C x).hom.app F = comparison F x := sorry

/-- Inverse components of `natIso` are the explicit stalk inverses. -/
@[simp, stacks 007Z "sheafification stalk natural isomorphism inverse component"]
theorem natIso_inv_app (C : Type v) [Category.{u} C]
    [HasTerminal C] [HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    (natIso C x).inv.app F = comparisonInv F x := sorry

end TopCat.Presheaf.SheafificationStalk
