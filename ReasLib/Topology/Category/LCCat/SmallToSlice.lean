/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Sites
public import ReasLib.Topology.Sheaves.Pullback.Sections
public import ReasLib.Topology.Sheaf.ExtensionByInitial.Constant
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous

/-!
# Inverse images from the small open site to a slice site

This leaf owns the source-facing model for the inverse image from the small open site of an
`LCCat` object to its localized slice sites.  The underlying presheaf is the functor of sections
of pullbacks over `⊤`; its sheaf proofs and the comparison maps are kept as separate API facts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace LCCat.SmallToSlice

variable (X : LCCat.{u})

/-- The pullback-section rule on the slice over `X`, functorial in the small-site sheaf. -/
@[stacks 09X3 "the pullback-section rule"]
noncomputable def rule :
    X.obj.Sheaf (Type u) ⥤ (Over X)ᵒᵖ ⥤ Type u :=
  TopCat.Sheaf.PullbackSections.functor (C := Type u) LCCat.toTopCat X (⊤ : Opens X.obj)

/-- The value of `rule` at `Y ⟶ X` is sections of the pullback sheaf over the top open of `Y`.
The map is the canonical transport along `Opens.map_top`. -/
@[stacks 09X3 "pullback-section rule at an object"]
noncomputable def ruleObjIso (F : X.obj.Sheaf (Type u)) (Y : Over X) :
    ((rule X).obj F).obj (op Y) ≅
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj F).presheaf.obj
        (op (⊤ : Opens Y.left.obj))) :=
  eqToIso (congrArg
    (fun U : Opens Y.left.obj ↦
      (((TopCat.Sheaf.pullback (Type u) Y.hom.hom).obj F).presheaf.obj (op U)))
    (Opens.map_top Y.hom.hom))

/-- The canonical small-to-slice functor is continuous for the Zariski localization. -/
@[stacks 09X3 "small-to-slice continuity"]
instance opensOver_isContinuous :
    Functor.IsContinuous (opensOver X) (Opens.grothendieckTopology X.obj)
      (zarTopology.over X) := sorry

/-- The canonical functor from the small open site to the Zariski slice site is fully faithful,
expressed without choosing preimages of morphisms. -/
@[stacks 0DCU "small-to-slice hom-set bijection"]
theorem opensOver_map_bijective (U V : Opens X.obj) :
    Function.Bijective
      ((opensOver X).map : (U ⟶ V) → ((opensOver X).obj U ⟶ (opensOver X).obj V)) := sorry

/-- The small-to-slice functor is full. -/
@[stacks 0DCU "small-to-slice fullness", instance]
instance opensOver_full : Functor.Full (opensOver X) := sorry

/-- The small-to-slice functor is faithful. -/
@[stacks 0DCU "small-to-slice faithfulness", instance]
instance opensOver_faithful : Functor.Faithful (opensOver X) := sorry

/-- The canonical small-to-slice functor is cocontinuous for the Zariski topology. -/
@[stacks 0DCU "small-to-slice cocontinuity", instance]
instance opensOver_isCocontinuous :
    Functor.IsCocontinuous (opensOver X) (Opens.grothendieckTopology X.obj)
      (zarTopology.over X) := sorry

/-- The canonical small-to-slice functor is almost cocontinuous for the Zariski topology. -/
@[stacks 0DCU "small-to-slice almost cocontinuity", instance]
instance opensOver_isAlmostCocontinuous :
    Functor.IsAlmostCocontinuous (opensOver X) (Opens.grothendieckTopology X.obj)
      (zarTopology.over X) := sorry

/-- The type-valued direct image along `opensOver X` has the right adjoint needed for the
small-to-slice sheaf adjunction. -/
@[stacks 09X3 "small-to-slice right adjoint"]
instance opensOver_type_pushforward_isRightAdjoint
    [HasWeakSheafify (zarTopology.over X) (Type u)] :
    ((opensOver X).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology X.obj) (zarTopology.over X)).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (opensOver X) (Type u)
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)).isRightAdjoint

/-- The canonical small-to-slice functor is continuous for the qc localization. -/
@[stacks 0D92 "small-to-qc continuity"]
instance opensOver_isContinuous_qc :
    Functor.IsContinuous (opensOver X) (Opens.grothendieckTopology X.obj)
      (qcTopology.over X) := sorry

/- The two functor-level inverse images are named here so later chapters can use the canonical
   small-to-slice data directly, without rebuilding notation around a chosen site functor. -/

/-- The Type-valued inverse image from the small open site to the Zariski slice site. -/
@[stacks 0DCU "small-to-slice Type inverse image"]
noncomputable abbrev typePullback
    [HasWeakSheafify (zarTopology.over X) (Type u)] :
    X.obj.Sheaf (Type u) ⥤ Sheaf (zarTopology.over X) (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback (opensOver X) (Type u)
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)

/-- The Type-valued inverse image from the small open site to the qc slice site. -/
@[stacks 0D92 "small-to-qc Type inverse image"]
noncomputable abbrev qcTypePullback [HasWeakSheafify (qcTopology.over X) (Type u)] :
    X.obj.Sheaf (Type u) ⥤ Sheaf (qcTopology.over X) (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback (opensOver X) (Type u)
    (Opens.grothendieckTopology X.obj) (qcTopology.over X)

/-- The restriction-level comparison between the pullback-section rule and the original small
site sheaf. -/
@[stacks 09X3 "small-to-slice restriction comparison"]
noncomputable def restrictionIso (F : X.obj.Sheaf (Type u)) :
    (opensOver X).op ⋙ (rule X).obj F ≅ F.presheaf :=
  NatIso.ofComponents
    (fun U ↦
      (((TopCat.Sheaf.pullback (Type u) (Opens.inclusion' U.unop)).obj F).presheaf.mapIso
        (eqToIso (congrArg op (Opens.map_top (Opens.inclusion' U.unop))))) ≪≫
        TopCat.Sheaf.ExtensionByInitial.Constant.pullbackTopSectionIso U.unop F)
    (fun φ ↦ sorry)

/-- The pullback-section rule is a sheaf for the quasi-compact topology. -/
@[stacks 09X3 "09X3 (1): qc sheaf"]
theorem isSheafQc (F : X.obj.Sheaf (Type u)) :
    Presheaf.IsSheaf (qcTopology.over X) ((rule X).obj F) := sorry

/-- The pullback-section rule is also a sheaf for the Zariski topology. -/
@[stacks 09X3 "09X3 (2): Zariski sheaf"]
theorem isSheafZar (F : X.obj.Sheaf (Type u)) :
    Presheaf.IsSheaf (zarTopology.over X) ((rule X).obj F) := sorry

/-- The Zariski sheaf represented by the pullback-section rule. -/
@[stacks 09X3 "Zariski pullback sections"]
noncomputable def zar :
    X.obj.Sheaf (Type u) ⥤ Sheaf (zarTopology.over X) (Type u) :=
  ObjectProperty.lift _ (rule X) (isSheafZar X)

/-- The explicit restriction morphism into the direct image of the Zariski rule. -/
@[stacks 09X3 "small-to-slice restriction morphism"]
noncomputable def restrictionHom (F : X.obj.Sheaf (Type u)) :
    F ⟶
      ((opensOver X).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology X.obj) (zarTopology.over X)).obj ((zar X).obj F) :=
  ObjectProperty.homMk (restrictionIso X F).inv

/-- The canonical map from the abstract sheaf pullback to the pullback-section model. -/
@[stacks 09X3 "small-to-slice sections comparison"]
noncomputable def sectionsComparison
    [HasWeakSheafify (zarTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    (Functor.sheafPullbackConstruction.sheafPullback (opensOver X) (Type u)
      (Opens.grothendieckTopology X.obj) (zarTopology.over X)).obj F ⟶ (zar X).obj F :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (opensOver X) (Type u)
      (Opens.grothendieckTopology X.obj) (zarTopology.over X)).homEquiv F ((zar X).obj F)).symm
    (restrictionHom X F)

/-- The small-to-slice sections comparison is invertible. -/
@[stacks 09X3 "small-to-slice sections comparison isomorphism"]
theorem sectionsComparison_isIso
    [HasWeakSheafify (zarTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    IsIso (sectionsComparison X F) := sorry

/-- The qc sheaf represented by the pullback-section rule. -/
@[stacks 09X3 "qc pullback sections"]
noncomputable def qc [HasWeakSheafify (qcTopology.over X) (Type u)] :
    X.obj.Sheaf (Type u) ⥤ Sheaf (qcTopology.over X) (Type u) :=
  ObjectProperty.lift _ (rule X) (isSheafQc X)

/-- The canonical comparison from the Zariski rule to the topology-comparison direct image of
the qc rule.  Its underlying presheaf map is the identity. -/
@[stacks 09X3 "09X3 (3): Zariski/qc comparison"]
noncomputable def pushforwardComparison [HasWeakSheafify (qcTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    (zar X).obj F ⟶
      (comparisonTopologyPushforward (Type u) zar_le_qc X).obj ((qc X).obj F) :=
  ObjectProperty.homMk (𝟙 ((rule X).obj F))

/-- The Zariski/qc comparison is invertible. -/
@[stacks 09X3 "Zariski/qc comparison isomorphism"]
theorem pushforwardComparison_isIso [HasWeakSheafify (qcTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    IsIso (pushforwardComparison X F) := sorry

/-- The canonical qc map obtained from the topology-comparison inverse image and counit. -/
@[stacks 09X3 "qc inverse-image comparison"]
noncomputable def qcComparison [HasWeakSheafify (qcTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    (comparisonTopologyPullback (Type u) zar_le_qc X).obj ((zar X).obj F) ⟶
      (qc X).obj F :=
  (comparisonTopologyPullback (Type u) zar_le_qc X).map (pushforwardComparison X F) ≫
    (comparisonTopologyAdjunction (Type u) zar_le_qc X).counit.app ((qc X).obj F)

/-- The qc inverse-image comparison is invertible. -/
@[stacks 09X3 "qc inverse-image comparison isomorphism"]
theorem qcComparison_isIso [HasWeakSheafify (qcTopology.over X) (Type u)]
    (F : X.obj.Sheaf (Type u)) :
    IsIso (qcComparison X F) := sorry

/-!
The next declarations isolate the geometric comparison used by the functoriality of the
small-open site.  The TopCat owner is deliberately exposed separately: it is useful whenever a
pullback along an open embedding is compared with an inverse-image open, independently of
`LCCat`.
-/

/-- The carrier of the inverse-image open is the preimage of the range of its inclusion. -/
@[stacks 09X3 "TopCat pullback/open carrier comparison"]
theorem pullbackOpenIsoTop_set {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Opens Y) :
    f ⁻¹' Set.range (Opens.inclusion' U) = ((Opens.map f).obj U : Set X) := sorry

/-- The TopCat pullback of an open inclusion is the inverse-image open of the other leg. -/
@[stacks 09X3 "TopCat pullback/open comparison"]
noncomputable def pullbackOpenIsoTop {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Opens Y) :
    pullback (Opens.inclusion' U) f ≅
      (Opens.toTopCat X).obj ((Opens.map f).obj U) :=
  TopCat.isoOfHomeo
    ((TopCat.homeoOfIso (pullbackSymmetry (Opens.inclusion' U) f)).trans
      ((TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype f (Opens.inclusion' U))).trans
        ((TopCat.pullbackHomeoPreimage f f.hom.continuous (Opens.inclusion' U)
          (Opens.isOpenEmbedding U).isEmbedding).trans
          (Homeomorph.setCongr (pullbackOpenIsoTop_set f U)))))

/-- The corresponding pullback/open comparison in `LCCat`. -/
@[stacks 09X3 "LCCat pullback/open comparison"]
noncomputable def pullbackOpenIso {X Y : LCCat.{u}} (f : X ⟶ Y) (U : Opens Y.obj) :
    pullback (openInclusion Y U) f ≅
      (opensToLCCat X).obj ((Opens.map f.hom).obj U) :=
  ObjectProperty.isoMk property
    ((PreservesPullback.iso LCCat.toTopCat (openInclusion Y U) f) ≪≫
      pullbackOpenIsoTop f.hom U)

/-- The triangle equation for the concrete pullback/open comparison. -/
@[stacks 09X3 "LCCat pullback/open comparison triangle"]
theorem pullbackOpenIso_fac {X Y : LCCat.{u}} (f : X ⟶ Y) (U : Opens Y.obj) :
    (pullbackOpenIso f U).hom ≫
        (openInclusion X ((Opens.map f.hom).obj U)) =
      pullback.snd (openInclusion Y U) f := sorry

/-- The objectwise over-category isomorphism induced by `pullbackOpenIso`. -/
@[stacks 09X3 "small-open pullback component"]
noncomputable def pullbackOpenOverIso {X Y : LCCat.{u}} (f : X ⟶ Y) (U : Opens Y.obj) :
    ((opensOver Y ⋙ Over.pullback f).obj U) ≅
      ((Opens.map f.hom ⋙ opensOver X).obj U) :=
  Over.isoMk (pullbackOpenIso f U) (pullbackOpenIso_fac f U)

/-- Naturality of the objectwise small-open pullback comparison. -/
@[stacks 09X3 "small-open pullback component naturality"]
theorem pullbackOpenOverIso_naturality {X Y : LCCat.{u}} (f : X ⟶ Y)
    {U V : Opens Y.obj} (i : U ⟶ V) :
    ((opensOver Y ⋙ Over.pullback f).map i) ≫ (pullbackOpenOverIso f V).hom =
      (pullbackOpenOverIso f U).hom ≫ ((Opens.map f.hom ⋙ opensOver X).map i) := sorry

/-- Canonical comparison of the small-open site with pullback along a map of `LCCat` spaces. -/
@[stacks 09X3 "small-open pullback functoriality", stacks 0DCU "(5)"]
noncomputable def opensOver_compIso {X Y : LCCat.{u}} (f : X ⟶ Y) :
    opensOver Y ⋙ Over.pullback f ≅ Opens.map f.hom ⋙ opensOver X :=
  NatIso.ofComponents (fun U ↦ pullbackOpenOverIso f U)
    (fun i ↦ pullbackOpenOverIso_naturality f i)

end LCCat.SmallToSlice

end
