/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem
public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Higher direct images along affine-transition inverse systems
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (S : Scheme.{u})
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, D.obj (OrderDual.toDual i) ⟶ S)
variable (hg : ∀ (i j : I) (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap D hij ≫ g i = g j)
variable (c : Cone D)
variable (gX : c.pt ⟶ S)
variable (hgX : ∀ i : I, c.π.app (OrderDual.toDual i) ≫ g i = gX)
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [hSheafify_pt : HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [hAbelian_pt : Abelian (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [hInjectiveResolutions_pt :
    HasInjectiveResolutions (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem D) (p : ℕ)

/-- The adjunction unit from a stage sheaf to its transition pushforward. -/
def higherDirectImage_unit {i j : I} (hij : i ≤ j) :
    schemeHigherDirectImage (g i) (F.obj i) p ⟶
      schemeHigherDirectImage (g i)
        (((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPushforwardContinuous
            AddCommGrpCat.{u}
            (D.obj (OrderDual.toDual i)).smallEtaleTopology
            (D.obj (OrderDual.toDual j)).smallEtaleTopology).obj
          ((transitionPullback D hij).obj (F.obj i))) p :=
  schemeHigherDirectImageMap (g i)
    (((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafAdjunctionContinuous
        AddCommGrpCat.{u}
        (D.obj (OrderDual.toDual i)).smallEtaleTopology
        (D.obj (OrderDual.toDual j)).smallEtaleTopology).unit.app (F.obj i)) p

/-- The site isomorphism induced by the commuting triangle of structure maps. -/
def structureSiteCompIso {i j : I} (hij : i ≤ j) :
    smallEtalePullback (g i) ⋙
        smallEtalePullback (OrderDualInverseSystem.transitionMap D hij) ≅
      smallEtalePullback (g j) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (OrderDualInverseSystem.transitionMap D hij) (g i) (g j) (hg i j hij).symm).symm

/-- The underived pushforward composition isomorphism for a transition. -/
def structurePushforwardCompIso {i j : I} (hij : i ≤ j) :
    (smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPushforwardContinuous
          AddCommGrpCat.{u}
          (D.obj (OrderDual.toDual i)).smallEtaleTopology
          (D.obj (OrderDual.toDual j)).smallEtaleTopology ⋙
        (smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology ≅
      (smallEtalePullback (g j)).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology :=
  schemePushforwardCompIso (structureSiteCompIso S D g hg hij)

include hg

/-- The one-way derived comparison associated to a transition triangle. -/
def higherDirectImage_structureComp {i j : I} (hij : i ≤ j)
    (G : Sheaf (D.obj (OrderDual.toDual j)).smallEtaleTopology AddCommGrpCat.{u}) :
    schemeHigherDirectImage (g i)
        (((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPushforwardContinuous
            AddCommGrpCat.{u}
            (D.obj (OrderDual.toDual i)).smallEtaleTopology
            (D.obj (OrderDual.toDual j)).smallEtaleTopology).obj G) p ⟶
      schemeHigherDirectImage (g j) G p :=
  (Functor.RightDerived.precompComparison
      ((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (D.obj (OrderDual.toDual i)).smallEtaleTopology
        (D.obj (OrderDual.toDual j)).smallEtaleTopology)
      ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology) p).app G ≫
    (CategoryTheory.NatTrans.rightDerived (structurePushforwardCompIso S D g hg hij).hom p).app G

/-- The transition map between the stage higher direct images. -/
def higherDirectImageDiagramMap (i j : I) (hij : i ≤ j) :
    schemeHigherDirectImage (g i) (F.obj i) p ⟶
      schemeHigherDirectImage (g j) (F.obj j) p :=
  higherDirectImage_unit S D g F p hij ≫
    schemeHigherDirectImageMap (g i)
      (((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPushforwardContinuous
          AddCommGrpCat.{u}
          (D.obj (OrderDual.toDual i)).smallEtaleTopology
          (D.obj (OrderDual.toDual j)).smallEtaleTopology).map
        (F.transition hij)) p ≫
    higherDirectImage_structureComp S D g hg p hij (F.obj j)

/-- The transition maps compose on three comparable indices. -/
theorem higherDirectImageDiagramMap_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    higherDirectImageDiagramMap S D g hg F p i k (le_trans hij hjk) =
      higherDirectImageDiagramMap S D g hg F p i j hij ≫
        higherDirectImageDiagramMap S D g hg F p j k hjk := sorry

/-- The diagram of stage higher direct images retains the original preorder transitions. -/
def higherDirectImageDiagram :
    PreorderWithAdjoinedIdentities I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => schemeHigherDirectImage (g i) (F.obj i) p)
    (fun {i j} hij => higherDirectImageDiagramMap S D g hg F p i j hij)
    (fun {i j k} hij hjk => higherDirectImageDiagramMap_comp S D g hg F p hij hjk)

/-- Evaluating the higher-direct-image diagram at a stage gives its defining stage object. -/
theorem higherDirectImageDiagram_obj (i : I) :
    (higherDirectImageDiagram S D g hg F p).obj i =
      schemeHigherDirectImage (g i) (F.obj i) p :=
  rfl

/-- The adjunction unit along a cone projection, pushed to higher direct images. -/
def higherDirectImage_unitCone (i : I) :
    schemeHigherDirectImage (g i) (F.obj i) p ⟶
      schemeHigherDirectImage (g i)
        (((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
            AddCommGrpCat.{u}
            (D.obj (OrderDual.toDual i)).smallEtaleTopology
            c.pt.smallEtaleTopology).obj
          ((conePullback D c i).obj (F.obj i))) p :=
  schemeHigherDirectImageMap (g i)
    (((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafAdjunctionContinuous
        AddCommGrpCat.{u}
        (D.obj (OrderDual.toDual i)).smallEtaleTopology
        c.pt.smallEtaleTopology).unit.app (F.obj i)) p

include c gX hgX hSheafify_pt hAbelian_pt

/-- The site isomorphism induced by a cone projection and its structure map. -/
def coneSiteCompIso (i : I) :
    smallEtalePullback (g i) ⋙ smallEtalePullback (c.π.app (OrderDual.toDual i)) ≅
      smallEtalePullback gX :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (c.π.app (OrderDual.toDual i)) (g i) gX (hgX i).symm).symm

/-- The underived pushforward composition isomorphism for a cone projection. -/
def conePushforwardCompIso (i : I) :
    (smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
          AddCommGrpCat.{u}
          (D.obj (OrderDual.toDual i)).smallEtaleTopology
          c.pt.smallEtaleTopology ⋙
        (smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology ≅
      (smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology c.pt.smallEtaleTopology :=
  schemePushforwardCompIso (coneSiteCompIso S D g c gX hgX i)

/-- The one-way derived comparison from a cone-stage pushforward to the limit pushforward. -/
def higherDirectImage_coneComp (i : I)
    (G : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :
    schemeHigherDirectImage (g i)
        (((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
            AddCommGrpCat.{u}
            (D.obj (OrderDual.toDual i)).smallEtaleTopology
            c.pt.smallEtaleTopology).obj G) p ⟶
    schemeHigherDirectImage gX G p :=
  let _comm := hgX i
  -- Local instance justification (defeq pin): use the canonical cone-point sheaf abelian structure.
  letI hConeAbelian : Abelian (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :=
    sheafIsAbelian
  -- Local instance justification (defeq pin): identify the constant-diagram site with the cone-point site.
  letI : HasSheafify (((Functor.const (OrderDual I)).obj c.pt).obj
      (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u})
  let hConeAdditive : ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
      AddCommGrpCat.{u} (D.obj (OrderDual.toDual i)).smallEtaleTopology
      c.pt.smallEtaleTopology).Additive := inferInstance
  let hConePreservesInjective : ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
      AddCommGrpCat.{u} (D.obj (OrderDual.toDual i)).smallEtaleTopology
      c.pt.smallEtaleTopology).PreservesInjectiveObjects :=
    smallEtalePushforward_preservesInjectiveObjects _
  let hStructureAdditive : ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology).Additive :=
    inferInstance
  let hCompositeAdditive :
      ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
          AddCommGrpCat.{u} (D.obj (OrderDual.toDual i)).smallEtaleTopology
          c.pt.smallEtaleTopology ⋙
        (smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology).Additive :=
    ⟨by
      intro X Y f h
      simp only [Functor.comp_map]
      rw [hConeAdditive.map_add, hStructureAdditive.map_add]
      rfl⟩
  let hLimitAdditive : ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology c.pt.smallEtaleTopology).Additive := inferInstance
  (@Functor.RightDerived.precompComparison
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) _ hConeAbelian
      (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) _ inferInstance
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) _ inferInstance
      ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (D.obj (OrderDual.toDual i)).smallEtaleTopology
        c.pt.smallEtaleTopology)
      hConeAdditive hConePreservesInjective
      hInjectiveResolutions_pt inferInstance
      ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology (D.obj (OrderDual.toDual i)).smallEtaleTopology)
      hStructureAdditive p).app G ≫
    (@CategoryTheory.NatTrans.rightDerived
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) _
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) _ hConeAbelian
      hInjectiveResolutions_pt inferInstance _ _ hCompositeAdditive hLimitAdditive
      (conePushforwardCompIso S D g c gX hgX i).hom p).app G

include c gX hgX

/-- The map from a stage higher direct image to the higher direct image of the colimit sheaf. -/
def higherDirectImageStageMap
    [HasColimit (inverseImageDiagram D c F)] (i : I) :
    schemeHigherDirectImage (g i) (F.obj i) p ⟶
    schemeHigherDirectImage gX (colimitInverseImage D c F) p :=
  let _comm := hgX i
  higherDirectImage_unitCone S D g c F p i ≫
    schemeHigherDirectImageMap (g i)
      (((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
          AddCommGrpCat.{u}
          (D.obj (OrderDual.toDual i)).smallEtaleTopology
          c.pt.smallEtaleTopology).map
        (colimit.ι (inverseImageDiagram D c F) i)) p ≫
    higherDirectImage_coneComp S D g c gX hgX p i (colimitInverseImage D c F)

/-- The stage maps are compatible with the original transition maps. -/
theorem higherDirectImageStageMap_naturality
    [HasColimit (inverseImageDiagram D c F)] {i j : I} (hij : i ≤ j) :
    higherDirectImageDiagramMap S D g hg F p i j hij ≫
        higherDirectImageStageMap (S := S) (D := D) (g := g) (c := c) (gX := gX)
          (hgX := hgX) (F := F) (p := p) j =
      higherDirectImageStageMap (S := S) (D := D) (g := g) (c := c) (gX := gX)
        (hgX := hgX) (F := F) (p := p) i := sorry

/-- The cocone of stage higher direct images with vertex the limit higher direct image. -/
def higherDirectImageCocone
    [HasColimit (inverseImageDiagram D c F)] :
    Cocone (higherDirectImageDiagram S D g hg F p) :=
  { pt := schemeHigherDirectImage gX (colimitInverseImage D c F) p
    ι :=
      { app := fun i => higherDirectImageStageMap (S := S) (D := D) (g := g) (c := c)
          (gX := gX) (hgX := hgX) (F := F) (p := p) i
        naturality := by
          apply (PreorderWithAdjoinedIdentities.lift_cocone_iff
            (fun i => schemeHigherDirectImage (g i) (F.obj i) p)
            (fun {i j} hij => higherDirectImageDiagramMap S D g hg F p i j hij)
            (fun {i j k} hij hjk => higherDirectImageDiagramMap_comp S D g hg F p hij hjk)
            _ (fun i => higherDirectImageStageMap (S := S) (D := D) (g := g) (c := c)
              (gX := gX) (hgX := hgX) (F := F) (p := p) i)).2
          intro i j hij
          exact higherDirectImageStageMap_naturality (S := S) (D := D) (g := g) (hg := hg)
            (c := c) (gX := gX) (hgX := hgX) (F := F) (p := p) hij } }

variable [HasColimit (inverseImageDiagram D c F)]
variable [HasColimit (higherDirectImageDiagram S D g hg F p)]

/-- The canonical comparison from the colimit of stage higher direct images to the limit
higher direct image of the colimit sheaf. -/
def higherDirectImageComparison :
    colimit (higherDirectImageDiagram S D g hg F p) ⟶
      schemeHigherDirectImage gX (colimitInverseImage D c F) p :=
  colimit.desc (higherDirectImageDiagram S D g hg F p)
    (higherDirectImageCocone (S := S) (D := D) (g := g) (hg := hg) (c := c)
      (gX := gX) (hgX := hgX) (F := F) (p := p))

/-- The canonical comparison restricts to the prescribed stage map on each colimit inclusion. -/
theorem higherDirectImageComparison_ι (i : I) :
    colimit.ι (higherDirectImageDiagram S D g hg F p) i ≫
        higherDirectImageComparison (S := S) (D := D) (g := g) (hg := hg) (c := c)
          (gX := gX) (hgX := hgX) (F := F) (p := p) =
      higherDirectImageStageMap (S := S) (D := D) (g := g) (c := c) (gX := gX)
        (hgX := hgX) (F := F) (p := p) i :=
  by
    simpa only [higherDirectImageComparison, higherDirectImageCocone] using
      colimit.ι_desc (higherDirectImageCocone (S := S) (D := D) (g := g) (hg := hg)
        (c := c) (gX := gX) (hgX := hgX) (F := F) (p := p)) i

/-- For a directed inverse limit of schemes with affine transitions and quasi-compact,
quasi-separated structure maps, higher direct images commute with the colimit of a compatible
system of abelian étale sheaves. -/
theorem higherDirectImage_colimit_affineTransition
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, QuasiCompact (g i)] [∀ i : I, QuasiSeparated (g i)]
    [QuasiCompact gX] [QuasiSeparated gX] (hc : IsLimit c) :
    IsIso (higherDirectImageComparison (S := S) (D := D) (g := g) (hg := hg) (c := c)
      (gX := gX) (hgX := hgX) (F := F) (p := p)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
