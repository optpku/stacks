module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.Topology.Opens.Inclusion
public import stacks_project.Chap85.Lemma_85_2_1_Opens
public import stacks_project.Chap85.Lemma_85_2_3
public import stacks_project.Chap85.Lemma_85_2_12_Projection

/-!
# Open preimage of an augmentation

The simplicial space `Y ×_X V` obtained by pulling an open of the augmented space back
along an augmentation, together with its open immersion into `Y` and restriction of
abelian sheaves to the Zariski site of the preimage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open TopCat.Opens.Subspace

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- The simplicial space `Y ×_X V` whose degree-`n` space is the open subspace
`a.app n ⁻¹ V ⊆ Y.obj n`. -/
def augmentationPreimage (V : Opens X) : SimplicialObject TopCat.{u} where
  obj n := TopCat.Opens.Subspace.space ((Opens.map (a.app n)).obj V)
  map {n m} f :=
    (DiagramOpens.toTopCat Y).map
      (DiagramOpens.homMk f sorry :
        DiagramOpens.ofOpens Y n ((Opens.map (a.app n)).obj V) ⟶
          DiagramOpens.ofOpens Y m ((Opens.map (a.app m)).obj V))
  map_id := sorry
  map_comp := sorry

/-- Degree-`n` evaluation of `augmentationPreimage a V` is the open subspace
`(Opens.map (a.app n)).obj V`. -/
theorem augmentationPreimage_obj (V : Opens X) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimage a V).obj n =
      TopCat.Opens.Subspace.space ((Opens.map (a.app n)).obj V) :=
  sorry

/-- The open immersion of simplicial spaces `Y ×_X V ⟶ Y`. -/
def augmentationPreimageι (V : Opens X) :
    augmentationPreimage a V ⟶ Y where
  app n := TopCat.Opens.Subspace.inclusion ((Opens.map (a.app n)).obj V)
  naturality := sorry

/-- The degree-`n` component of `augmentationPreimageι a V` is the open-subspace inclusion. -/
theorem augmentationPreimageι_app (V : Opens X) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimageι a V).app n =
      TopCat.Opens.Subspace.inclusion ((Opens.map (a.app n)).obj V) :=
  sorry

/-- The morphism of simplicial spaces `Y ×_X V ⟶ Y ×_X W` induced by `V ≤ W`. -/
def augmentationPreimageιOfLE {V W : Opens X} (h : V ≤ W) :
    augmentationPreimage a V ⟶ augmentationPreimage a W where
  app n :=
    TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app n)).map (homOfLE h)))
  naturality := sorry

/-- The degree-`n` component of `augmentationPreimageιOfLE` is the nested open-subspace map. -/
theorem augmentationPreimageιOfLE_app {V W : Opens X} (h : V ≤ W) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimageιOfLE a h).app n =
      TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app n)).map (homOfLE h))) :=
  sorry

/-- The functor sending an open of `Y ×_X V` to the same open viewed in `Y_Zar`. -/
def augmentationPreimageSiteι (V : Opens X) :
    zariskiSite (augmentationPreimage a V) ⥤ zariskiSite Y where
  obj U :=
    DiagramOpens.ofOpens Y U.base
      ((((Opens.map (a.app U.base)).obj V).isOpenEmbedding.functor).obj U.opens)
  map f := DiagramOpens.homMk f.base sorry
  map_id := sorry
  map_comp := sorry

/-- Continuity of the site inclusion of opens of `Y ×_X V` into `Y_Zar`. -/
instance augmentationPreimageSiteι_isContinuous (V : Opens X) :
    (augmentationPreimageSiteι a V).IsContinuous
      (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y) :=
  sorry

/-- Restriction of abelian sheaves from `Y_Zar` to `(Y ×_X V)_Zar`, as continuous
precomposition along the site inclusion of opens of the preimage. -/
abbrev restrictAugmentationPreimage (V : Opens X) :
    Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u} :=
  (augmentationPreimageSiteι a V).sheafPushforwardContinuous AddCommGrpCat.{u}
    (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y)

/-- Restriction to `(Y ×_X V)_Zar` is continuous sheaf pushforward along
`augmentationPreimageSiteι a V`. -/
theorem restrictAugmentationPreimage_obj (V : Opens X)
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    (restrictAugmentationPreimage a V).obj F =
      ((augmentationPreimageSiteι a V).sheafPushforwardContinuous AddCommGrpCat.{u}
        (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y)).obj F :=
  sorry

/-- The functor sending an open of `Y ×_X V` to the same open viewed in `(Y ×_X W)_Zar`,
for `V ≤ W`. -/
def augmentationPreimageSiteMapOfLE {V W : Opens X} (h : V ≤ W) :
    zariskiSite (augmentationPreimage a V) ⥤ zariskiSite (augmentationPreimage a W) where
  obj U :=
    DiagramOpens.ofOpens (augmentationPreimage a W) U.base
      ((homOfLE_isOpenEmbedding
          (leOfHom ((Opens.map (a.app U.base)).map (homOfLE h)))).functor.obj U.opens)
  map f := DiagramOpens.homMk f.base sorry
  map_id := sorry
  map_comp := sorry

/-- Continuity of the site inclusion `(Y ×_X V)_Zar ⥤ (Y ×_X W)_Zar` for `V ≤ W`. -/
instance augmentationPreimageSiteMapOfLE_isContinuous {V W : Opens X} (h : V ≤ W) :
    (augmentationPreimageSiteMapOfLE a h).IsContinuous
      (zariskiTopology (augmentationPreimage a V))
      (zariskiTopology (augmentationPreimage a W)) :=
  sorry

/-- Cocontinuity of the site inclusion `(Y ×_X V)_Zar ⥤ (Y ×_X W)_Zar` for `V ≤ W`. -/
instance augmentationPreimageSiteMapOfLE_isCocontinuous {V W : Opens X} (h : V ≤ W) :
    (augmentationPreimageSiteMapOfLE a h).IsCocontinuous
      (zariskiTopology (augmentationPreimage a V))
      (zariskiTopology (augmentationPreimage a W)) :=
  sorry

/-- Restriction of abelian sheaves from `(Y ×_X W)_Zar` to `(Y ×_X V)_Zar` along `V ≤ W`. -/
abbrev restrictAugmentationPreimageOfLE {V W : Opens X} (h : V ≤ W) :
    Sheaf (zariskiTopology (augmentationPreimage a W)) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u} :=
  (augmentationPreimageSiteMapOfLE a h).sheafPushforwardContinuous AddCommGrpCat.{u}
    (zariskiTopology (augmentationPreimage a V))
    (zariskiTopology (augmentationPreimage a W))

/-- Restriction along `V ≤ W` preserves finite limits. -/
instance restrictAugmentationPreimageOfLE_preservesFiniteLimits {V W : Opens X} (h : V ≤ W) :
    PreservesFiniteLimits (restrictAugmentationPreimageOfLE a h) :=
  sorry

/-- Restriction along `V ≤ W` preserves finite colimits. -/
instance restrictAugmentationPreimageOfLE_preservesFiniteColimits {V W : Opens X} (h : V ≤ W) :
    PreservesFiniteColimits (restrictAugmentationPreimageOfLE a h) :=
  sorry

/-- Continuity of the composite site functor through `(Y ×_X W)_Zar`. -/
instance augmentationPreimageSiteι_le_comp_isContinuous {V W : Opens X} (h : V ≤ W) :
    (augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W).IsContinuous
      (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y) :=
  sorry

/-- Identity-stage comparison from the site inclusion of `Y ×_X V` into `Y_Zar` to the
composite through `(Y ×_X W)_Zar`. -/
def augmentationPreimageSiteι_leNatTrans {V W : Opens X} (h : V ≤ W) :
    augmentationPreimageSiteι a V ⟶
      augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W where
  app U := DiagramOpens.homMk (𝟙 U.base) sorry
  naturality := sorry

end CategoryTheory.SimplicialObject
