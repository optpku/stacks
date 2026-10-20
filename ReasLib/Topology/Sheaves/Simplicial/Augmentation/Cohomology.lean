/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Cohomology
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pullback

/-!
# Augmentation cohomology presheaf

The presheaf on `Opens X` sending `V` to the Zariski cohomology of the restriction of an
abelian sheaf to `(Y ×_X V)_Zar`, and its sheafification.
-/

-- Private declaration justification (module visibility): retain private implementation
-- names while allowing the exposed constructions to use their bodies.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Functor Opposite TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)
variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
variable [∀ V : Opens X,
    HasSheafify (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}]
variable [∀ V : Opens X,
    HasExt.{u} (Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The comparison `ℤ̲_{Y ×_X V} ⟶ (restrict along V ≤ W)(ℤ̲_{Y ×_X W})`. -/
def augmentationIntegerRestrictHom {V W : Opens X} (h : V ≤ W) :
    constantIntegerSheaf (zariskiTopology (augmentationPreimage a V)) ⟶
      (restrictAugmentationPreimageOfLE a h).obj
        (constantIntegerSheaf (zariskiTopology (augmentationPreimage a W))) :=
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  let u := augmentationPreimageSiteMapOfLE a h
  let adjV := sheafificationAdjunction (zariskiTopology (augmentationPreimage a V))
    AddCommGrpCat.{u}
  let adjW := sheafificationAdjunction (zariskiTopology (augmentationPreimage a W))
    AddCommGrpCat.{u}
  (adjV.homEquiv ((Functor.const (zariskiSite (augmentationPreimage a V))ᵒᵖ).obj M)
      ((restrictAugmentationPreimageOfLE a h).obj
        (constantIntegerSheaf (zariskiTopology (augmentationPreimage a W))))).symm
    ((constCompWhiskeringLeftIso (zariskiSite (augmentationPreimage a V))ᵒᵖ u.op).inv.app M ≫
      whiskerLeft u.op (adjW.unit.app ((Functor.const (zariskiSite (augmentationPreimage a W))ᵒᵖ).obj M)))

/-- The restriction map
`H^n((Y ×_X W)_Zar, F|_(Y ×_X W)) ⟶ H^n((Y ×_X V)_Zar, F|_(Y ×_X V))` for `V ≤ W`. -/
def augmentationCohomologyRestrict {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    zariskiCohomology (augmentationPreimage a W) ((restrictAugmentationPreimage a W).obj F) n ⟶
      zariskiCohomology (augmentationPreimage a V) ((restrictAugmentationPreimage a V).obj F) n :=
  AddCommGrpCat.ofHom
    ((restrictAugmentationPreimageOfLE a h).mapExtAddHom
      (constantIntegerSheaf (zariskiTopology (augmentationPreimage a W)))
      ((restrictAugmentationPreimage a W).obj F) n) ≫
    AddCommGrpCat.ofHom
      ((Ext.mk₀ (augmentationIntegerRestrictHom a h)).precomp
        ((restrictAugmentationPreimageOfLE a h).obj
          ((restrictAugmentationPreimage a W).obj F)) (zero_add n)) ≫
    (zariskiCohomologyFunctor (augmentationPreimage a V) n).map
      (restrictAugmentationPreimage_leHom a h F)

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Cohomological restriction along the identity inclusion is the identity map. -/
private theorem augmentationCohomologyRestrict_id
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) (V : (Opens X)ᵒᵖ) :
    augmentationCohomologyRestrict a (leOfHom (𝟙 V).unop) F n = 𝟙 _ := by
  sorry

omit [HasExt.{u} (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Cohomological restriction along a composite inclusion is the composite of restrictions. -/
private theorem augmentationCohomologyRestrict_comp
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ)
    {U V W : (Opens X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    augmentationCohomologyRestrict a (leOfHom (f ≫ g).unop) F n =
      augmentationCohomologyRestrict a (leOfHom f.unop) F n ≫
        augmentationCohomologyRestrict a (leOfHom g.unop) F n := by
  sorry

/-- The presheaf on `Opens X` sending `V` to
`H^n((Y ×_X V)_Zar, F|_(Y ×_X V)_Zar)`. -/
def augmentationCohomologyPresheaf (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V :=
    zariskiCohomology (augmentationPreimage a V.unop) ((restrictAugmentationPreimage a V.unop).obj F) n
  map {V W} f :=
    augmentationCohomologyRestrict a (leOfHom f.unop) F n
  map_id := augmentationCohomologyRestrict_id a F n
  map_comp := augmentationCohomologyRestrict_comp a F n

/-- Evaluating the augmentation cohomology presheaf recovers Zariski cohomology of the
restricted sheaf. -/
theorem augmentationCohomologyPresheaf_obj (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens X) :
    (augmentationCohomologyPresheaf a F n).obj (op V) =
      zariskiCohomology (augmentationPreimage a V) ((restrictAugmentationPreimage a V).obj F) n :=
  rfl

/-- The sheaf on `X` associated to the augmentation cohomology presheaf. -/
def sheafifiedAugmentationCohomology (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (augmentationCohomologyPresheaf a F n)

/-- Sheafification of the augmentation cohomology presheaf is `presheafToSheaf` of that
presheaf. -/
theorem sheafifiedAugmentationCohomology_obj (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) :
    sheafifiedAugmentationCohomology a F n =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (augmentationCohomologyPresheaf a F n) :=
  rfl

end CategoryTheory.SimplicialObject
