/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : AbelianSheafSystem DX) (p : ℕ)


/-- The degree-`p` higher direct image of `F.obj i` along the stage morphism `g i`. -/
def stageHigherDirectImage (i : I) :
    Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  schemeHigherDirectImage (g i) (F.obj i) p


/-- The stage higher direct image pulled back along the projection of the base cone. -/
def pullbackStageHigherDirectImage (i : I) :
    Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback (cS.π.app (OrderDual.toDual i))).sheafPullback AddCommGrpCat.{u}
      (DS.obj (OrderDual.toDual i)).smallEtaleTopology cS.pt.smallEtaleTopology |>.obj
    (stageHigherDirectImage DX DS g F p i)


/-- Transition compatibility identifies the source-side composite of small étale
pullbacks with pullback along the base-side composite scheme morphism. -/
def structureSiteCompIso {i j : I} (hij : i ≤ j) :
    smallEtalePullback (g i) ⋙
        smallEtalePullback (OrderDualInverseSystem.transitionMap DX hij) ≅
      smallEtalePullback (g j ≫ OrderDualInverseSystem.transitionMap DS hij) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (OrderDualInverseSystem.transitionMap DX hij) (g i)
      (g j ≫ OrderDualInverseSystem.transitionMap DS hij) (hg hij).symm).symm


/-- The base-side composite of small étale pullbacks identifies with pullback
along the composite scheme morphism. -/
def structureSiteCompIso_base {i j : I} (hij : i ≤ j) :
    smallEtalePullback (OrderDualInverseSystem.transitionMap DS hij) ⋙
        smallEtalePullback (g j) ≅
      smallEtalePullback (g j ≫ OrderDualInverseSystem.transitionMap DS hij) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (g j) (OrderDualInverseSystem.transitionMap DS hij)
      (g j ≫ OrderDualInverseSystem.transitionMap DS hij) rfl).symm


/-- Transition compatibility identifies the two composites of underived direct images. -/
def structurePushforwardCompIso {i j : I} (hij : i ≤ j) :
    (smallEtalePullback (OrderDualInverseSystem.transitionMap DX hij)).sheafPushforwardContinuous
          AddCommGrpCat.{u} (DX.obj (OrderDual.toDual i)).smallEtaleTopology
          (DX.obj (OrderDual.toDual j)).smallEtaleTopology ⋙
        (smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (DS.obj (OrderDual.toDual i)).smallEtaleTopology
          (DX.obj (OrderDual.toDual i)).smallEtaleTopology ≅
      (smallEtalePullback (g j)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (DS.obj (OrderDual.toDual j)).smallEtaleTopology
          (DX.obj (OrderDual.toDual j)).smallEtaleTopology ⋙
        (smallEtalePullback (OrderDualInverseSystem.transitionMap DS hij)).sheafPushforwardContinuous
          AddCommGrpCat.{u} (DS.obj (OrderDual.toDual i)).smallEtaleTopology
          (DS.obj (OrderDual.toDual j)).smallEtaleTopology :=
  Functor.sheafPushforwardContinuousComp'
      (structureSiteCompIso DX DS g hg hij) AddCommGrpCat.{u}
      (DS.obj (OrderDual.toDual i)).smallEtaleTopology (DX.obj (OrderDual.toDual i)).smallEtaleTopology
      (DX.obj (OrderDual.toDual j)).smallEtaleTopology ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (structureSiteCompIso_base DX DS g hij) AddCommGrpCat.{u}
      (DS.obj (OrderDual.toDual i)).smallEtaleTopology (DS.obj (OrderDual.toDual j)).smallEtaleTopology
      (DX.obj (OrderDual.toDual j)).smallEtaleTopology).symm


/-- Sheafification on the cone point is also available on each constant-diagram stage. -/
instance conePointX_hasSheafify (i : I) :
    HasSheafify (((Functor.const (OrderDual I)).obj cX.pt).obj
        (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u})

/-- Weak sheafification on the cone point is available on each constant-diagram stage. -/
instance conePointX_hasWeakSheafify (i : I) :
    HasWeakSheafify (((Functor.const (OrderDual I)).obj cX.pt).obj
        (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u})

/-- Injective resolutions on the cone point are available on each constant-diagram stage. -/
instance conePointX_hasInjectiveResolutions (i : I) :
    HasInjectiveResolutions
      (Sheaf (((Functor.const (OrderDual I)).obj cX.pt).obj
          (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}))

/-- Cone naturality and the transition counit give a comparison from pulled-back
transition direct image to pullback along the later projection. -/
def baseConePullbackMap (i j : I) (hij : i ≤ j)
    (G : Sheaf (DS.obj (OrderDual.toDual j)).smallEtaleTopology AddCommGrpCat.{u}) :
    (conePullback DS cS i).obj
      (((smallEtalePullback (OrderDualInverseSystem.transitionMap DS hij)).sheafPushforwardContinuous
        AddCommGrpCat.{u} (DS.obj (OrderDual.toDual i)).smallEtaleTopology
        (DS.obj (OrderDual.toDual j)).smallEtaleTopology).obj G) ⟶
      (conePullback DS cS j).obj G :=
  (conePullbackCompIso DS cS hij).inv.app _ ≫
    (conePullback DS cS j).map
      (((smallEtalePullback (OrderDualInverseSystem.transitionMap DS hij)).sheafAdjunctionContinuous
        AddCommGrpCat.{u} (DS.obj (OrderDual.toDual i)).smallEtaleTopology
        (DS.obj (OrderDual.toDual j)).smallEtaleTopology).counit.app G)

namespace HigherDirectImage.InverseSystem

/-- The reflexive scheme transitions form a commutative square with a stage morphism. -/
theorem selfSquare (i : I) :
    OrderDualInverseSystem.transitionMap DX (le_refl i) ≫ g i =
      g i ≫ OrderDualInverseSystem.transitionMap DS (le_refl i) := sorry

/-- The reflexive transition on a pulled-back higher direct image is defined independently
of a family of compatibility equations. -/
def diagonal (i : I) :
    pullbackStageHigherDirectImage DX DS g cS F p i ⟶
      pullbackStageHigherDirectImage DX DS g cS F p i :=
  (conePullbackCompIso DS cS (le_refl i)).inv.app _ ≫
    (conePullback DS cS i).map
      ((HigherDirectImage.baseChange (g i) (g i)
        (OrderDualInverseSystem.transitionMap DX (le_refl i))
        (OrderDualInverseSystem.transitionMap DS (le_refl i))
        (selfSquare DX DS g i) p).app (F.obj i) ≫
          schemeHigherDirectImageMap (g i) (F.transition (le_refl i)) p)

/-- Pulled-back higher direct images transition by base change followed by the sheaf transition. -/
def transition {i j : I} (hij : i ≤ j) :
    pullbackStageHigherDirectImage DX DS g cS F p i ⟶
      pullbackStageHigherDirectImage DX DS g cS F p j :=
  (conePullbackCompIso DS cS hij).inv.app _ ≫
    (conePullback DS cS j).map
      ((HigherDirectImage.baseChange (g i) (g j)
        (OrderDualInverseSystem.transitionMap DX hij)
        (OrderDualInverseSystem.transitionMap DS hij) (hg hij) p).app (F.obj i) ≫
          schemeHigherDirectImageMap (g j) (F.transition hij) p)

/-- The higher-direct-image transitions compose through every intermediate stage. -/
theorem transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition DX DS g hg cS F p (le_trans hij hjk) =
      transition DX DS g hg cS F p hij ≫ transition DX DS g hg cS F p hjk := sorry

/-- The raw diagram retains the original pulled-back stage objects and reflexive transitions,
with genuine categorical identities adjoined separately. -/
def diagram :
    PreorderWithAdjoinedIdentities I ⥤ Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.lift
    (pullbackStageHigherDirectImage DX DS g cS F p)
    (fun {i j} hij => transition DX DS g hg cS F p hij)
    (fun {i j k} hij hjk => transition_comp DX DS g hg cS F p hij hjk)

/-- Each raw diagram object is the original pulled-back stage higher direct image. -/
theorem diagram_obj (i : I) :
    (diagram DX DS g hg cS F p).obj i =
      pullbackStageHigherDirectImage DX DS g cS F p i := rfl

variable [HasColimit (inverseImageDiagram DX cX F)]

/-- Cone-square base change followed by the colimit inclusion gives the stage comparison. -/
def stageMap (i : I) :
    pullbackStageHigherDirectImage DX DS g cS F p i ⟶
      schemeHigherDirectImage gX (colimitInverseImage DX cX F) p :=
  (HigherDirectImage.baseChange (g i) gX (cX.π.app (OrderDual.toDual i))
    (cS.π.app (OrderDual.toDual i)) (hgX i) p).app (F.obj i) ≫
      schemeHigherDirectImageMap gX (colimitInverseImage_ι DX cX F i) p

/-- The stage comparisons are compatible with all raw transition maps. -/
theorem stageMap_naturality {i j : I} (hij : i ≤ j) :
    transition DX DS g hg cS F p hij ≫ stageMap DX DS g cX cS gX hgX F p j =
      stageMap DX DS g cX cS gX hgX F p i := sorry

/-- The raw stage comparisons form a cocone with vertex the higher direct image
of the inverse-image colimit. -/
def cocone : Cocone (diagram DX DS g hg cS F p) :=
  let compatibility : ∀ {i j : PreorderWithAdjoinedIdentities I} (arrow : i ⟶ j),
      (diagram DX DS g hg cS F p).map arrow ≫ stageMap DX DS g cX cS gX hgX F p j =
        stageMap DX DS g cX cS gX hgX F p i :=
    (PreorderWithAdjoinedIdentities.lift_cocone_iff
    (pullbackStageHigherDirectImage DX DS g cS F p)
    (fun {i j} hij => transition DX DS g hg cS F p hij)
    (fun {i j k} hij hjk => transition_comp DX DS g hg cS F p hij hjk)
    (schemeHigherDirectImage gX (colimitInverseImage DX cX F) p)
    (stageMap DX DS g cX cS gX hgX F p)).mpr
      (fun {i j} hij => stageMap_naturality DX DS g hg cX cS gX hgX F p hij)
  { pt := schemeHigherDirectImage gX (colimitInverseImage DX cX F) p
    ι :=
      { app := stageMap DX DS g cX cS gX hgX F p
        naturality := fun i j arrow =>
          (compatibility arrow).trans
            (Category.comp_id (stageMap DX DS g cX cS gX hgX F p i)).symm } }

/-- Colimit descent constructs the canonical raw higher-direct-image comparison. -/
def comparison [HasColimit (diagram DX DS g hg cS F p)] :
    colimit (diagram DX DS g hg cS F p) ⟶
      schemeHigherDirectImage gX (colimitInverseImage DX cX F) p :=
  colimit.desc (diagram DX DS g hg cS F p) (cocone DX DS g hg cX cS gX hgX F p)

end HigherDirectImage.InverseSystem

/-- For a directed inverse system of quasi-compact quasi-separated scheme morphisms
with affine transitions on both sides, the raw higher-direct-image comparison is
an isomorphism in every nonnegative degree. -/
theorem higherDirectImage_colimit_inverseSystemOfMorphisms
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    [∀ i : I, QuasiCompact (g i)] [∀ i : I, QuasiSeparated (g i)]
    [HasColimit (inverseImageDiagram DX cX F)]
    [HasColimit (HigherDirectImage.InverseSystem.diagram DX DS g hg cS F p)]
    (hcX : IsLimit cX) (hcS : IsLimit cS) :
    IsIso (HigherDirectImage.InverseSystem.comparison DX DS g hg cX cS gX hgX F p) := sorry

end AlgebraicGeometry.Scheme.Etale

end
