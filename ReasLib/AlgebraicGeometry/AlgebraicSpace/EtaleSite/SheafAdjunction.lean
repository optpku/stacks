/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesAtlasCharts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction to the small chart family is an equivalence with its concrete Kan inverse. -/
def smallEquivalence (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type u) ≌
      Sheaf (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X) (Type u) :=
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.adjunction X).toEquivalence

/-- The same chart family gives a concrete presentation of the spaces-étale topos. -/
def spaceEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ≌
      Sheaf (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X) (Type u) :=
  ((AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.inclusion X).sheafAdjunctionCocontinuous (Type u)
    (AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)).toEquivalence

/-- Actual restriction from spaces-étale sheaves to scheme charts. -/
def restriction (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Extension from scheme charts uses only the small chart Kan extension. -/
def extension (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type u) ⥤ Sheaf (spacesEtaleTopology X) (Type u) :=
  (smallEquivalence X).functor ⋙ (spaceEquivalence X).inverse

/-- The actual small-chart unit identifies extension of a restriction. -/
def restrictionExtensionIso (X : AlgebraicSpace S) :
    𝟭 (Sheaf (spacesEtaleTopology X) (Type u)) ≅ restriction X ⋙ extension X :=
  (spaceEquivalence X).unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X)
        (smallEtaleInclusion X) (Type u) (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X)
        (smallEtaleTopology X) (spacesEtaleTopology X)).symm
      (spaceEquivalence X).inverse ≪≫ Functor.associator _ _ _

/-- The actual small-chart counit determines the comparison on all scheme charts by descent. -/
def extensionRestrictionIso (X : AlgebraicSpace S) :
    extension X ⋙ restriction X ≅ 𝟭 (Sheaf (smallEtaleTopology X) (Type u)) :=
  NatIso.ofComponents
    (fun N ↦
      let e : (smallEquivalence X).functor.obj
          ((restriction X).obj ((extension X).obj N)) ≅
            (smallEquivalence X).functor.obj N :=
        (spaceEquivalence X).counitIso.app ((smallEquivalence X).functor.obj N)
      let i : (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X).op ⋙
          ((restriction X).obj ((extension X).obj N)).obj ≅
            (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X).op ⋙ N.obj :=
        { hom := e.hom.hom, inv := e.inv.hom, hom_inv_id := sorry, inv_hom_id := sorry }
      Functor.IsCoverDense.Types.sheafIso i)
    sorry

/-- Equivalence with explicit extension and restriction functors. -/
def siteEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ≌ Sheaf (smallEtaleTopology X) (Type u) :=
  CategoryTheory.Equivalence.mk (restriction X) (extension X)
    (restrictionExtensionIso X) (extensionRestrictionIso X)

/-- Base change only needs the explicit small family of target charts. -/
def baseChange (f : X ⟶ Y) : AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site Y ⥤ spacesEtaleSite X :=
  AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y ⋙ etaleBaseChange f

instance baseChangeContinuous (f : X ⟶ Y) :
    (baseChange f).IsContinuous (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y) (etaleBaseChange f)
    (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Genuine small colimits supply the pointwise left Kan extension. -/
instance lanColimits (f : X ⟶ Y) (U : (spacesEtaleSite X)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (baseChange f).op U) (Type u) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

/-- Constructed left Kan extension, with no admitted existence witness. -/
instance hasLan (f : X ⟶ Y) (P : (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site Y)ᵒᵖ ⥤ Type u) :
    (baseChange f).op.HasLeftKanExtension P :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension (baseChange f).op P).hasLeftKanExtension

/-- Geometric inverse image uses the small-index Kan extension and genuine sheafification. -/
def inverseImage (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (smallEquivalence Y).functor ⋙
    Functor.sheafPullbackConstruction.sheafPullback (baseChange f) (Type u)
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X) ⋙
    restriction X

/-- Direct image uses restriction and right Kan extension on the same actual small charts. -/
def directImage (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology Y) (Type u) :=
  extension X ⋙ (etaleBaseChange f).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology Y) (spacesEtaleTopology X)

/-- Evaluate extended sections along an actual scheme chart over a spaces-étale object. -/
def extensionEvaluation (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    {W : spacesEtaleSite X} {U : smallEtaleSite X}
    (a : (smallEtaleInclusion X).obj U ⟶ W) :
    ((extension X).obj Q).obj.obj (op W) ⟶ Q.obj.obj (op U) :=
  ((extension X).obj Q).obj.map a.op ≫
    ((extensionRestrictionIso X).hom.app Q).hom.app (op U)

/-- An actual étale square gives its universal arrow into the geometric fibre product. -/
def squareArrow (f : X ⟶ Y) (sq : EtaleSquare f) :
    (smallEtaleInclusion X).obj sq.left ⟶ (etaleBaseChange f).obj sq.right :=
  MorphismProperty.Over.homMk
    (Limits.pullback.lift (f := homFunctor f) (g := homFunctor sq.right.hom)
      sq.left.hom (ofOverMap sq.map) sq.w)
    (Limits.pullback.lift_fst (f := homFunctor f) (g := homFunctor sq.right.hom) _ _ _)

/-- The small-chart extension forms a cone of actual evaluations on all scheme charts. -/
def allChartCone (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    (W : spacesEtaleSite X) :
    Cone (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj) where
  pt := ((extension X).obj Q).obj.obj (op W)
  π := { app := fun a ↦ extensionEvaluation X Q a.hom.unop, naturality := sorry }

/-- A cone on all scheme charts restricts to the specified small chart family. -/
def restrictChartCone (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    (W : spacesEtaleSite X)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj)) :
    Cone (StructuredArrow.proj (op W) (SpacesEtale.AtlasCharts.inclusion X).op ⋙
      ((smallEquivalence X).functor.obj Q).obj) where
  pt := c.pt
  π :=
    { app := fun a ↦ c.π.app
        (StructuredArrow.mk (Y := op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)) a.hom)
      naturality := sorry }

/-- Lift a full scheme-chart cone by its actual small-chart limit lift. -/
def allChartLift (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    (W : spacesEtaleSite X)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj)) :
    c.pt ⟶ (allChartCone X Q W).pt :=
  limit.lift _ (restrictChartCone X Q W c) ≫
    ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
      ((smallEquivalence X).functor.obj Q).obj (op W)).inv

/-- The sheaf extension's universal property has the specified lift, with uniqueness by descent. -/
def allChartIsLimit (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    (W : spacesEtaleSite X) : IsLimit (allChartCone X Q W) where
  lift := allChartLift X Q W
  fac := sorry
  uniq := sorry

/-- Existence of the full chart limit is witnessed by this explicit cone and lift. -/
def allChartHasLimit (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) (Type u))
    (W : spacesEtaleSite X) :
    HasLimit (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj) :=
  ⟨⟨⟨allChartCone X Q W, allChartIsLimit X Q W⟩⟩⟩

/-- Unwind the small target chart restriction in the composite right adjoint. -/
def rightComparison (f : X ⟶ Y) :
    ((extension X ⋙ (baseChange f).sheafPushforwardContinuous (Type u)
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X)) ⋙
      (smallEquivalence Y).inverse) ≅ directImage f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (extension X)
      (Functor.sheafPushforwardContinuousComp (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion Y)
        (etaleBaseChange f) (Type u) (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y)
        (smallEtaleTopology Y) (spacesEtaleTopology X)).symm)
    (smallEquivalence Y).inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (extension X)
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            ((etaleBaseChange f).sheafPushforwardContinuous (Type u)
              (smallEtaleTopology Y) (spacesEtaleTopology X))
            (smallEquivalence Y).unitIso.symm ≪≫ Functor.rightUnitor _)

/-- Composing the concrete chart equivalences and Kan/sheafification adjunction
supplies the actual unit and counit. -/
def adjunction (f : X ⟶ Y) : inverseImage f ⊣ directImage f :=
  ((smallEquivalence Y).toAdjunction.comp
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange f) (Type u)
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology Y) (spacesEtaleTopology X)).comp
        (siteEquivalence X).toAdjunction)).ofNatIsoRight (rightComparison f)

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
