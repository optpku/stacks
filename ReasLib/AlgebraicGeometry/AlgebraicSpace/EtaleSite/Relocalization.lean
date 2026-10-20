module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Étale relocalization of algebraic spaces

The functor `i_f` sends an étale scheme over an algebraic space `Y` to the same
object of `Over X` along a morphism `f : Y ⟶ X`. Inverse image of abelian
sheaves is precomposition with this functor. The spaces-étale relocalization
functor similarly gives restriction as the inverse image of a geometric morphism
and admits a lower-shriek left adjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- The relocalization functor from the small étale site of `Y` to the big
étale slice site over `X`. -/
abbrev relocalizationFunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    smallEtaleSite Y ⥤ Over X :=
  smallEtaleToSpaces Y ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y ⋙ Over.map f

/-- The structural morphism of a relocalized chart is its original morphism
followed by the morphism of algebraic spaces. -/
theorem relocalizationFunctor_obj_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (U : smallEtaleSite Y) :
    ((relocalizationFunctor f).obj U).hom = U.hom ≫ f := rfl

/-- The relocalization functor is continuous for the small-to-big étale topologies. -/
instance relocalizationFunctor_isContinuous {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Functor.IsContinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X) :=
  sorry

/-- The relocalization functor is cocontinuous for the small-to-big étale topologies. -/
instance relocalizationFunctor_isCocontinuous {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    Functor.IsCocontinuous (relocalizationFunctor f) (smallEtaleTopology Y)
      (overEtaleTopology X) :=
  sorry

/-- Inverse image of abelian sheaves along étale relocalization. -/
abbrev inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (overEtaleTopology X)

/-- Sections of the inverse-image sheaf are sections of the original sheaf
at the relocalized chart. -/
theorem inverseImage_obj_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (F : Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite Y) :
    ((inverseImage f).obj F).obj.obj (Opposite.op U) =
      F.obj.obj (Opposite.op ((relocalizationFunctor f).obj U)) := rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale
namespace SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The relocalization functor from the spaces-étale site of `Y` to the big
étale slice site over `X`. -/
abbrev relocalizationFunctor (f : Y ⟶ X) : spacesEtaleSite Y ⥤ Over X :=
  MorphismProperty.Over.forget (@Etale S) ⊤ Y ⋙ Over.map f

/-- Relocalization sends `j : U ⟶ Y` to `j ≫ f : U ⟶ X`. -/
theorem relocalizationFunctor_obj_hom (f : Y ⟶ X) (U : spacesEtaleSite Y) :
    ((relocalizationFunctor f).obj U).hom = U.hom ≫ f := rfl

/-- The relocalization functor is continuous for the spaces-to-big étale
topologies. -/
instance relocalizationFunctor_isContinuous (f : Y ⟶ X) :
    Functor.IsContinuous (relocalizationFunctor f) (spacesEtaleTopology Y)
      (overEtaleTopology X) := sorry

/-- The relocalization functor is cocontinuous for the spaces-to-big étale
topologies. -/
instance relocalizationFunctor_isCocontinuous (f : Y ⟶ X) :
    Functor.IsCocontinuous (relocalizationFunctor f) (spacesEtaleTopology Y)
      (overEtaleTopology X) := sorry

/-- Spaces-étale relocalization preserves fibre products. -/
instance Relocalization.preservesPullbacks (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (relocalizationFunctor f) := sorry

/-- Spaces-étale relocalization preserves equalizers. -/
instance Relocalization.preservesEqualizers (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingParallelPair (relocalizationFunctor f) := sorry

/-- The opposite relocalization functor admits pointwise left Kan extensions
with coefficients in a universe containing its comma categories. -/
instance relocalizationFunctor_op_hasPointwiseLeftKanExtension
    [UnivLE.{u + 1, w}] (f : Y ⟶ X) (P : (spacesEtaleSite Y)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseLeftKanExtension P :=
  fun _ ↦ inferInstance

/-- The opposite relocalization functor admits left Kan extensions
with coefficients in a universe containing its comma categories. -/
instance relocalizationFunctor_op_hasLeftKanExtension
    [UnivLE.{u + 1, w}] (f : Y ⟶ X) (P : (spacesEtaleSite Y)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := inferInstance

/-- The opposite relocalization functor admits pointwise right Kan extensions
with coefficients in a universe containing its comma categories. -/
instance relocalizationFunctor_op_hasPointwiseRightKanExtension
    [UnivLE.{u + 1, w}] (f : Y ⟶ X) (P : (spacesEtaleSite Y)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- The inverse-image functor on sheaves induced by spaces-étale relocalization. -/
abbrev inverseImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) (Type w) ⥤
      Sheaf (spacesEtaleTopology Y) (Type w) :=
  (relocalizationFunctor f).sheafPushforwardContinuous (Type w)
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The inverse image is computed by evaluating on the same algebraic space
viewed over `X`. -/
theorem inverseImage_obj_obj (f : Y ⟶ X)
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) (U : spacesEtaleSite Y) :
    ((inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) := rfl

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : Y ⟶ X)
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) (U : spacesEtaleSite Y) :
    ((inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (relocalizationFunctor f) (Type w) 𝒢 U

/-- The inverse-image objectwise comparison is natural in the spaces-étale
object. -/
theorem inverseImage_objObjIso_naturality (f : Y ⟶ X)
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) {U V : spacesEtaleSite Y}
    (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.1.map ((relocalizationFunctor f).map φ).op =
      ((inverseImage f).obj 𝒢).1.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The lower-shriek functor on spaces-étale sheaves. -/
abbrev lowerShriek (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    Sheaf (spacesEtaleTopology Y) (Type w) ⥤
      Sheaf (overEtaleTopology X) (Type w) :=
  (relocalizationFunctor f).sheafPullback (Type w) (spacesEtaleTopology Y)
    (overEtaleTopology X)

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- Lower shriek preserves fibre products. -/
theorem lowerShriek_preservesPullbacks (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasSheafify (overEtaleTopology X) (Type w)] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasSheafify (overEtaleTopology X) (Type w)] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

/-- The lower-shriek adjunction agrees with the canonical continuous-site
adjunction. -/
theorem lowerShriekAdjunction_def (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    lowerShriekAdjunction f =
      (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
        (spacesEtaleTopology Y) (overEtaleTopology X) := rfl

/-- The inverse image is a right adjoint whenever lower shriek is available. -/
instance inverseImage_isRightAdjoint (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    (inverseImage.{u, w} f).IsRightAdjoint :=
  (lowerShriekAdjunction f).isRightAdjoint

/-- The direct-image functor presented by the cocontinuous relocalization
functor. -/
abbrev directImage (f : Y ⟶ X) [UnivLE.{u + 1, w}] :
    Sheaf (spacesEtaleTopology Y) (Type w) ⥤
      Sheaf (overEtaleTopology X) (Type w) :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous (Type w)
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The small atlas-chart family of `Y`, viewed as algebraic spaces over `X`. -/
def smallChartFunctor (f : Y ⟶ X) :
    SmallEtale.AtlasCharts.Site Y ⥤ Over X :=
  SpacesEtale.AtlasCharts.inclusion Y ⋙ relocalizationFunctor f

/-- The chart functor to the big étale slice is continuous. -/
instance smallChartFunctor_isContinuous (f : Y ⟶ X) :
    (smallChartFunctor f).IsContinuous (SpacesEtale.AtlasCharts.topology Y)
      (overEtaleTopology X) :=
  Functor.isContinuous_comp (SpacesEtale.AtlasCharts.inclusion Y)
    (relocalizationFunctor f) (SpacesEtale.AtlasCharts.topology Y)
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The chart functor to the big étale slice is cocontinuous. -/
instance smallChartFunctor_isCocontinuous (f : Y ⟶ X) :
    (smallChartFunctor f).IsCocontinuous (SpacesEtale.AtlasCharts.topology Y)
      (overEtaleTopology X) :=
  isCocontinuous_comp (SpacesEtale.AtlasCharts.inclusion Y)
    (relocalizationFunctor f) (SpacesEtale.AtlasCharts.topology Y)
    (spacesEtaleTopology Y)

/-- Chart comma categories admit Type-valued limits in the base universe. -/
instance smallChartFunctor_rightKanLimits (f : Y ⟶ X) (U : (Over X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (smallChartFunctor f).op) (Type u) :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The small-source chart functor admits actual pointwise right Kan extensions. -/
instance smallChartFunctor_op_hasPointwiseRightKanExtension (f : Y ⟶ X)
    (P : (SmallEtale.AtlasCharts.Site Y)ᵒᵖ ⥤ Type u) :
    (smallChartFunctor f).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- Direct image of Type-valued sheaves via restriction to small atlas charts
and right Kan extension to the big étale slice. -/
def directImageTypeU (f : Y ⟶ X) :
    Sheaf (spacesEtaleTopology Y) (Type u) ⥤
      Sheaf (overEtaleTopology X) (Type u) :=
  (EtaleTopos.spaceEquivalence Y).functor ⋙
    (smallChartFunctor f).sheafPushforwardCocontinuous (Type u)
      (SpacesEtale.AtlasCharts.topology Y) (overEtaleTopology X)

/-- Direct image is chart restriction followed by the chart right Kan extension. -/
theorem directImageTypeU_def (f : Y ⟶ X) :
    directImageTypeU f =
      (EtaleTopos.spaceEquivalence Y).functor ⋙
        (smallChartFunctor f).sheafPushforwardCocontinuous (Type u)
          (SpacesEtale.AtlasCharts.topology Y) (overEtaleTopology X) := rfl

/-- Extending the chart restriction of an inverse image recovers that inverse image. -/
private def inverseImageChartExtensionIso (f : Y ⟶ X) :
    (smallChartFunctor f).sheafPushforwardContinuous (Type u)
        (SpacesEtale.AtlasCharts.topology Y) (overEtaleTopology X) ⋙
      (EtaleTopos.spaceEquivalence Y).inverse ≅ inverseImage f :=
  Functor.isoWhiskerRight
    (Functor.sheafPushforwardContinuousComp (SpacesEtale.AtlasCharts.inclusion Y)
      (relocalizationFunctor f) (Type u) (SpacesEtale.AtlasCharts.topology Y)
      (spacesEtaleTopology Y) (overEtaleTopology X)).symm
    (EtaleTopos.spaceEquivalence Y).inverse ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (inverseImage f) (EtaleTopos.spaceEquivalence Y).unitIso.symm ≪≫
  Functor.rightUnitor _

/-- Restriction to the spaces-étale site is left adjoint to the small-chart direct image. -/
@[no_expose] def inverseImageDirectImageAdjunctionTypeU (f : Y ⟶ X) :
    inverseImage f ⊣ directImageTypeU f :=
  (((smallChartFunctor f).sheafAdjunctionCocontinuous (Type u)
      (SpacesEtale.AtlasCharts.topology Y) (overEtaleTopology X)).comp
    (EtaleTopos.spaceEquivalence Y).symm.toAdjunction).ofNatIsoLeft
      (inverseImageChartExtensionIso f)

/-- The relocalization inverse image preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by spaces-étale relocalization. -/
noncomputable def morphismOfTopoi (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasSheafify (spacesEtaleTopology Y) (Type w)] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, w}
      (overEtaleTopology X) (spacesEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (relocalizationFunctor f).sheafAdjunctionCocontinuous (Type w)
      (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The inverse-image projection of the cocontinuously presented morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasSheafify (spacesEtaleTopology Y) (Type w)] :
    (morphismOfTopoi f)⁻¹ = inverseImage f := rfl

/-- The direct-image projection of the cocontinuously presented morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasSheafify (spacesEtaleTopology Y) (Type w)] :
    (morphismOfTopoi f).pushforward = directImage f := rfl

/-- The inverse-image computation through the bundled relocalization morphism. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : Y ⟶ X) [UnivLE.{u + 1, w}] [HasSheafify (spacesEtaleTopology Y) (Type w)]
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) (U : spacesEtaleSite Y) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  inverseImage_objObjIso f 𝒢 U

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : Y ⟶ X) [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    [HasSheafify (spacesEtaleTopology Y) (Type w)] :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  lowerShriekAdjunction f

end SpacesToBig
end Etale

end AlgebraicGeometry.AlgebraicSpace

end
