/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap85.Lemma_85_2_10_Cohomology
public import stacks_project.Chap85.Lemma_85_2_11_Pullback

/-!
# Augmentation cohomology presheaf

The presheaf on `Opens X` sending `V` to the Zariski cohomology of the restriction of an
abelian sheaf to `(Y ×_X V)_Zar`, and its sheafification.
-/

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

/-- The constant sheaf of integers on the Zariski site of a simplicial space. -/
abbrev zariskiIntegerSheaf (Z : SimplicialObject TopCat.{u})
    [HasSheafify (zariskiTopology Z) AddCommGrpCat.{u}] :
    Sheaf (zariskiTopology Z) AddCommGrpCat.{u} :=
  (constantSheaf (zariskiTopology Z) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- `zariskiIntegerSheaf Z` is the constant sheaf with value `ULift ℤ`. -/
theorem zariskiIntegerSheaf_eq (Z : SimplicialObject TopCat.{u})
    [HasSheafify (zariskiTopology Z) AddCommGrpCat.{u}] :
    zariskiIntegerSheaf Z =
      (constantSheaf (zariskiTopology Z) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  sorry

/-- The comparison `ℤ̲_{Y ×_X V} ⟶ (restrict along V ≤ W)(ℤ̲_{Y ×_X W})`. -/
def augmentationIntegerRestrictHom {V W : Opens X} (h : V ≤ W) :
    zariskiIntegerSheaf (augmentationPreimage a V) ⟶
      (restrictAugmentationPreimageOfLE a h).obj
        (zariskiIntegerSheaf (augmentationPreimage a W)) :=
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  let u := augmentationPreimageSiteMapOfLE a h
  let adjV := sheafificationAdjunction (zariskiTopology (augmentationPreimage a V))
    AddCommGrpCat.{u}
  let adjW := sheafificationAdjunction (zariskiTopology (augmentationPreimage a W))
    AddCommGrpCat.{u}
  (adjV.homEquiv ((Functor.const (zariskiSite (augmentationPreimage a V))ᵒᵖ).obj M)
      ((restrictAugmentationPreimageOfLE a h).obj
        (zariskiIntegerSheaf (augmentationPreimage a W)))).symm
    ((constCompWhiskeringLeftIso (zariskiSite (augmentationPreimage a V))ᵒᵖ u.op).inv.app M ≫
      whiskerLeft u.op (adjW.unit.app ((Functor.const (zariskiSite (augmentationPreimage a W))ᵒᵖ).obj M)))

/-- The identity-stage comparison of restrictions of an ambient sheaf along `V ≤ W`. -/
def restrictAugmentationPreimage_leHom {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    (restrictAugmentationPreimageOfLE a h).obj ((restrictAugmentationPreimage a W).obj F) ⟶
      (restrictAugmentationPreimage a V).obj F :=
  (sheafPushforwardContinuousNatTrans (augmentationPreimageSiteι_leNatTrans a h)
      AddCommGrpCat.{u} (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y)).app F

/-- The restriction map
`H^n((Y ×_X W)_Zar, F|_(Y ×_X W)) ⟶ H^n((Y ×_X V)_Zar, F|_(Y ×_X V))` for `V ≤ W`. -/
def augmentationCohomologyRestrict {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    zariskiCohomology (augmentationPreimage a W) ((restrictAugmentationPreimage a W).obj F) n ⟶
      zariskiCohomology (augmentationPreimage a V) ((restrictAugmentationPreimage a V).obj F) n :=
  AddCommGrpCat.ofHom
    ((restrictAugmentationPreimageOfLE a h).mapExtAddHom
      (zariskiIntegerSheaf (augmentationPreimage a W))
      ((restrictAugmentationPreimage a W).obj F) n) ≫
    AddCommGrpCat.ofHom
      ((Ext.mk₀ (augmentationIntegerRestrictHom a h)).precomp
        ((restrictAugmentationPreimageOfLE a h).obj
          ((restrictAugmentationPreimage a W).obj F)) (zero_add n)) ≫
    (zariskiCohomologyFunctor (augmentationPreimage a V) n).map
      (restrictAugmentationPreimage_leHom a h F)

/-- The presheaf on `Opens X` sending `V` to
`H^n((Y ×_X V)_Zar, F|_(Y ×_X V)_Zar)`. -/
def augmentationCohomologyPresheaf (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V :=
    zariskiCohomology (augmentationPreimage a V.unop) ((restrictAugmentationPreimage a V.unop).obj F) n
  map {V W} f :=
    augmentationCohomologyRestrict a (leOfHom f.unop) F n
  map_id := sorry
  map_comp := sorry

/-- Evaluating the augmentation cohomology presheaf recovers Zariski cohomology of the
restricted sheaf. -/
theorem augmentationCohomologyPresheaf_obj (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) (V : Opens X) :
    (augmentationCohomologyPresheaf a F n).obj (op V) =
      zariskiCohomology (augmentationPreimage a V) ((restrictAugmentationPreimage a V).obj F) n :=
  sorry

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
  sorry

end CategoryTheory.SimplicialObject
