module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.Topology.Opens.Inclusion
public import ReasLib.Topology.Category.TopCat.DiagramOpens
public import ReasLib.Topology.Category.TopCat.DiagramOpens.SimplicialMap
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

/-!
# Open preimage of an augmentation

The simplicial space `Y ×_X V` obtained by pulling an open of the augmented space back
along an augmentation, together with its open immersion into `Y` and restriction of
abelian sheaves to the Zariski site of the preimage.
-/

-- Private declaration justification (module visibility): retain private implementation
-- names while allowing the exposed constructions to use their bodies.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open TopCat.Opens.Subspace

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- Simplicial structure maps preserve the inverse image of an augmentation open. -/
private theorem augmentationPreimage_mapsTo (V : Opens X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    Set.MapsTo (Y.map f).hom ((Opens.map (a.app n)).obj V)
      ((Opens.map (a.app m)).obj V) := by
  sorry

/-- The map between open preimage subspaces induced by a simplicial structure map. -/
private def augmentationPreimageMap (V : Opens X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    TopCat.Opens.Subspace.space ((Opens.map (a.app n)).obj V) ⟶
      TopCat.Opens.Subspace.space ((Opens.map (a.app m)).obj V) :=
  (DiagramOpens.toTopCat Y).map
    (DiagramOpens.homMk f (augmentationPreimage_mapsTo a V f) :
      DiagramOpens.ofOpens Y n ((Opens.map (a.app n)).obj V) ⟶
        DiagramOpens.ofOpens Y m ((Opens.map (a.app m)).obj V))

/-- The induced map on an open preimage preserves identity morphisms. -/
private theorem augmentationPreimage_map_id (V : Opens X) (n : SimplexCategoryᵒᵖ) :
    augmentationPreimageMap a V (𝟙 n) = 𝟙 _ := by
  sorry

/-- The induced maps on open preimages preserve composition. -/
private theorem augmentationPreimage_map_comp (V : Opens X)
    {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) :
    augmentationPreimageMap a V (f ≫ g) =
      augmentationPreimageMap a V f ≫ augmentationPreimageMap a V g := by
  sorry

/-- The simplicial space `Y ×_X V` whose degree-`n` space is the open subspace
`a.app n ⁻¹ V ⊆ Y.obj n`. -/
def augmentationPreimage (V : Opens X) : SimplicialObject TopCat.{u} where
  obj n := TopCat.Opens.Subspace.space ((Opens.map (a.app n)).obj V)
  map f := augmentationPreimageMap a V f
  map_id := augmentationPreimage_map_id a V
  map_comp := augmentationPreimage_map_comp a V

/-- Degree-`n` evaluation of `augmentationPreimage a V` is the open subspace
`(Opens.map (a.app n)).obj V`. -/
theorem augmentationPreimage_obj (V : Opens X) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimage a V).obj n =
      TopCat.Opens.Subspace.space ((Opens.map (a.app n)).obj V) :=
  rfl

/-- The open-subspace inclusions commute with the simplicial structure maps. -/
private theorem augmentationPreimageι_naturality (V : Opens X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (augmentationPreimage a V).map f ≫
        TopCat.Opens.Subspace.inclusion ((Opens.map (a.app m)).obj V) =
      TopCat.Opens.Subspace.inclusion ((Opens.map (a.app n)).obj V) ≫ Y.map f := by
  sorry

/-- The open immersion of simplicial spaces `Y ×_X V ⟶ Y`. -/
def augmentationPreimageι (V : Opens X) :
    augmentationPreimage a V ⟶ Y where
  app n := TopCat.Opens.Subspace.inclusion ((Opens.map (a.app n)).obj V)
  naturality := fun _ _ f ↦ augmentationPreimageι_naturality a V f

/-- The degree-`n` component of `augmentationPreimageι a V` is the open-subspace inclusion. -/
theorem augmentationPreimageι_app (V : Opens X) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimageι a V).app n =
      TopCat.Opens.Subspace.inclusion ((Opens.map (a.app n)).obj V) :=
  rfl

/-- Inclusions between nested open preimages commute with simplicial structure maps. -/
private theorem augmentationPreimageιOfLE_naturality {V W : Opens X} (h : V ≤ W)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (augmentationPreimage a V).map f ≫
        TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app m)).map (homOfLE h))) =
      TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app n)).map (homOfLE h))) ≫
        (augmentationPreimage a W).map f := by
  sorry

/-- The morphism of simplicial spaces `Y ×_X V ⟶ Y ×_X W` induced by `V ≤ W`. -/
def augmentationPreimageιOfLE {V W : Opens X} (h : V ≤ W) :
    augmentationPreimage a V ⟶ augmentationPreimage a W where
  app n :=
    TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app n)).map (homOfLE h)))
  naturality := fun _ _ f ↦ augmentationPreimageιOfLE_naturality a h f

/-- The degree-`n` component of `augmentationPreimageιOfLE` is the nested open-subspace map. -/
theorem augmentationPreimageιOfLE_app {V W : Opens X} (h : V ≤ W) (n : SimplexCategoryᵒᵖ) :
    (augmentationPreimageιOfLE a h).app n =
      TopCat.Opens.Subspace.homOfLE (leOfHom ((Opens.map (a.app n)).map (homOfLE h))) :=
  rfl

/-- An open in a preimage subspace, viewed as an open of the ambient simplicial space. -/
private abbrev augmentationPreimageSiteιObj (V : Opens X)
    (U : zariskiSite (augmentationPreimage a V)) : zariskiSite Y :=
  DiagramOpens.ofOpens Y U.base
    ((((Opens.map (a.app U.base)).obj V).isOpenEmbedding.functor).obj U.opens)

/-- A morphism of preimage opens maps their ambient open images into one another. -/
private theorem augmentationPreimageSiteι_mapsTo (V : Opens X)
    {U W : zariskiSite (augmentationPreimage a V)} (f : U ⟶ W) :
    Set.MapsTo (Y.map f.base).hom
      (augmentationPreimageSiteιObj a V U).opens.carrier
      (augmentationPreimageSiteιObj a V W).opens.carrier := by
  sorry

/-- The ambient morphism induced by a morphism of preimage opens. -/
private def augmentationPreimageSiteιMap (V : Opens X)
    {U W : zariskiSite (augmentationPreimage a V)} (f : U ⟶ W) :
    augmentationPreimageSiteιObj a V U ⟶ augmentationPreimageSiteιObj a V W :=
  DiagramOpens.homMk f.base (augmentationPreimageSiteι_mapsTo a V f)

/-- Viewing preimage opens as ambient opens preserves identities. -/
private theorem augmentationPreimageSiteι_map_id (V : Opens X)
    (U : zariskiSite (augmentationPreimage a V)) :
    augmentationPreimageSiteιMap a V (𝟙 U) = 𝟙 _ := by
  sorry

/-- Viewing preimage opens as ambient opens preserves composition. -/
private theorem augmentationPreimageSiteι_map_comp (V : Opens X)
    {U W T : zariskiSite (augmentationPreimage a V)} (f : U ⟶ W) (g : W ⟶ T) :
    augmentationPreimageSiteιMap a V (f ≫ g) =
      augmentationPreimageSiteιMap a V f ≫ augmentationPreimageSiteιMap a V g := by
  sorry

/-- The functor sending an open of `Y ×_X V` to the same open viewed in `Y_Zar`. -/
def augmentationPreimageSiteι (V : Opens X) :
    zariskiSite (augmentationPreimage a V) ⥤ zariskiSite Y where
  obj := augmentationPreimageSiteιObj a V
  map f := augmentationPreimageSiteιMap a V f
  map_id := augmentationPreimageSiteι_map_id a V
  map_comp := augmentationPreimageSiteι_map_comp a V

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
  rfl

/-- An open in a smaller preimage, viewed as an open in a larger preimage. -/
private abbrev augmentationPreimageSiteMapOfLEObj {V W : Opens X} (h : V ≤ W)
    (U : zariskiSite (augmentationPreimage a V)) : zariskiSite (augmentationPreimage a W) :=
  DiagramOpens.ofOpens (augmentationPreimage a W) U.base
    ((homOfLE_isOpenEmbedding
        (leOfHom ((Opens.map (a.app U.base)).map (homOfLE h)))).functor.obj U.opens)

/-- A morphism of smaller preimage opens preserves their images in a larger preimage. -/
private theorem augmentationPreimageSiteMapOfLE_mapsTo {V W : Opens X} (h : V ≤ W)
    {U T : zariskiSite (augmentationPreimage a V)} (f : U ⟶ T) :
    Set.MapsTo ((augmentationPreimage a W).map f.base).hom
      (augmentationPreimageSiteMapOfLEObj a h U).opens.carrier
      (augmentationPreimageSiteMapOfLEObj a h T).opens.carrier := by
  sorry

/-- The morphism on opens induced by inclusion of nested preimages. -/
private def augmentationPreimageSiteMapOfLEMap {V W : Opens X} (h : V ≤ W)
    {U T : zariskiSite (augmentationPreimage a V)} (f : U ⟶ T) :
    augmentationPreimageSiteMapOfLEObj a h U ⟶ augmentationPreimageSiteMapOfLEObj a h T :=
  DiagramOpens.homMk f.base (augmentationPreimageSiteMapOfLE_mapsTo a h f)

/-- Inclusion of nested preimage sites preserves identities. -/
private theorem augmentationPreimageSiteMapOfLE_map_id {V W : Opens X} (h : V ≤ W)
    (U : zariskiSite (augmentationPreimage a V)) :
    augmentationPreimageSiteMapOfLEMap a h (𝟙 U) = 𝟙 _ := by
  sorry

/-- Inclusion of nested preimage sites preserves composition. -/
private theorem augmentationPreimageSiteMapOfLE_map_comp {V W : Opens X} (h : V ≤ W)
    {U T S : zariskiSite (augmentationPreimage a V)} (f : U ⟶ T) (g : T ⟶ S) :
    augmentationPreimageSiteMapOfLEMap a h (f ≫ g) =
      augmentationPreimageSiteMapOfLEMap a h f ≫ augmentationPreimageSiteMapOfLEMap a h g := by
  sorry

/-- The functor sending an open of `Y ×_X V` to the same open viewed in `(Y ×_X W)_Zar`,
for `V ≤ W`. -/
def augmentationPreimageSiteMapOfLE {V W : Opens X} (h : V ≤ W) :
    zariskiSite (augmentationPreimage a V) ⥤ zariskiSite (augmentationPreimage a W) where
  obj := augmentationPreimageSiteMapOfLEObj a h
  map f := augmentationPreimageSiteMapOfLEMap a h f
  map_id := augmentationPreimageSiteMapOfLE_map_id a h
  map_comp := augmentationPreimageSiteMapOfLE_map_comp a h

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

/-- The identity stage map preserves the open images along nested preimage inclusions. -/
private theorem augmentationPreimageSiteι_leNatTrans_mapsTo {V W : Opens X} (h : V ≤ W)
    (U : zariskiSite (augmentationPreimage a V)) :
    Set.MapsTo (Y.map (𝟙 U.base)).hom
      ((augmentationPreimageSiteι a V).obj U).opens.carrier
      ((augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W).obj U).opens.carrier := by
  sorry

/-- The identity stage comparison arrow between the two ambient open images. -/
private def augmentationPreimageSiteι_leNatTransApp {V W : Opens X} (h : V ≤ W)
    (U : zariskiSite (augmentationPreimage a V)) :
    (augmentationPreimageSiteι a V).obj U ⟶
      (augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W).obj U :=
  DiagramOpens.homMk (𝟙 U.base) (augmentationPreimageSiteι_leNatTrans_mapsTo a h U)

/-- The identity stage comparison commutes with morphisms of preimage opens. -/
private theorem augmentationPreimageSiteι_leNatTrans_naturality {V W : Opens X} (h : V ≤ W)
    {U T : zariskiSite (augmentationPreimage a V)} (f : U ⟶ T) :
    (augmentationPreimageSiteι a V).map f ≫ augmentationPreimageSiteι_leNatTransApp a h T =
      augmentationPreimageSiteι_leNatTransApp a h U ≫
        (augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W).map f := by
  sorry

/-- Identity-stage comparison from the site inclusion of `Y ×_X V` into `Y_Zar` to the
composite through `(Y ×_X W)_Zar`. -/
def augmentationPreimageSiteι_leNatTrans {V W : Opens X} (h : V ≤ W) :
    augmentationPreimageSiteι a V ⟶
      augmentationPreimageSiteMapOfLE a h ⋙ augmentationPreimageSiteι a W where
  app := augmentationPreimageSiteι_leNatTransApp a h
  naturality := fun _ _ f ↦ augmentationPreimageSiteι_leNatTrans_naturality a h f

/-- The identity-stage comparison of restrictions of an ambient sheaf along `V ≤ W`. -/
def restrictAugmentationPreimage_leHom {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :
    (restrictAugmentationPreimageOfLE a h).obj ((restrictAugmentationPreimage a W).obj F) ⟶
      (restrictAugmentationPreimage a V).obj F :=
  (sheafPushforwardContinuousNatTrans (augmentationPreimageSiteι_leNatTrans a h)
      AddCommGrpCat.{u} (zariskiTopology (augmentationPreimage a V)) (zariskiTopology Y)).app F

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [∀ V : Opens X,
    HasSheafify (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u}]

/-- Restriction to `(Y ×_X V)_Zar` preserves injective objects. -/
instance restrictAugmentationPreimage_preservesInjectiveObjects (V : Opens X) :
    (restrictAugmentationPreimage a V).PreservesInjectiveObjects :=
  sorry

/-- Restriction to `(Y ×_X V)_Zar` preserves homology. -/
instance restrictAugmentationPreimage_preservesHomology (V : Opens X) :
    (restrictAugmentationPreimage a V).PreservesHomology :=
  sorry

end CategoryTheory.SimplicialObject
