module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts
variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- A scheme atlas obtained from the supplied algebraic-space object's atlas witness. -/
def atlasOver : Over S := X.atlas.choose

/-- The atlas map carried by the algebraic-space object. -/
def atlasMap : yoneda.obj (atlasOver X) ⟶ X.functorOfPoints := X.atlas.choose_spec.choose

/-- The stored atlas has the required representable étale property. -/
theorem atlasMap_etale :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasMap X) :=
  X.atlas.choose_spec.choose_spec.1

/-- The stored atlas is locally surjective. -/
theorem atlasMap_surjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlasMap X) :=
  X.atlas.choose_spec.choose_spec.2

/-- The atlas as an object of the small étale site. -/
def atlasObject : smallEtaleSite X :=
  smallEtaleSite.mk (atlasMap X) ((SmallEtale.etale_iff _).mpr (atlasMap_etale X))

/-- A small family of affine charts over the supplied scheme atlas. -/
abbrev Index := SmallModel.{u} (atlasOver X).left.AffineEtale

/-- Interpret a small affine-chart index as a chart over the algebraic space. -/
def object (i : Index X) : smallEtaleSite X :=
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Sheafification.charts (atlasObject X)).obj
    ((Scheme.AffineEtale.Spec (atlasOver X).left).obj
      ((equivSmallModel.{u} (atlasOver X).left.AffineEtale).inverse.obj i))

/-- Retain all morphisms over the algebraic space between the small chart family. -/
def Site : Type u := InducedCategory (smallEtaleSite X) (object X)

/-- Morphisms retain the actual scheme maps from the original chart category. -/
instance : SmallCategory (Site X) :=
  inferInstanceAs (Category (InducedCategory (smallEtaleSite X) (object X)))

/-- The fully faithful inclusion of the explicit small chart family. -/
def inclusion : Site X ⥤ smallEtaleSite X := inducedFunctor (object X)

/-- The small chart inclusion has explicit preimages on Hom sets. -/
def fullyFaithful : (inclusion X).FullyFaithful := fullyFaithfulInducedFunctor (object X)

instance : (inclusion X).Full := (fullyFaithful X).full
instance : (inclusion X).Faithful := (fullyFaithful X).faithful

/-- The topology inherited by the small chart family. -/
def topology : GrothendieckTopology (Site X) :=
  (inclusion X).inducedTopology (smallEtaleTopology X)

/-- Every scheme chart is covered by affine charts of its pullback of the stored atlas. -/
instance coverDense : (inclusion X).IsCoverDense (smallEtaleTopology X) := sorry

/-- Full faithfulness and the induced topology give the dense-subsite structure. -/
instance dense : (inclusion X).IsDenseSubsite (topology X) (smallEtaleTopology X) := by
  dsimp [topology]
  infer_instance

/-- Small-site right Kan extensions exist by actual small limits. -/
instance hasRightKan (P : (Site X)ᵒᵖ ⥤ Type u) :
    (inclusion X).op.HasPointwiseRightKanExtension P := by
  intro U
  infer_instance

/-- The resulting cocontinuous extension uses the actual right Kan extension. -/
def extend : Sheaf (topology X) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (inclusion X).sheafPushforwardCocontinuous (Type u) (topology X) (smallEtaleTopology X)

/-- Restriction/extension adjunction with its actual Kan unit and counit. -/
def adjunction :
    (inclusion X).sheafPushforwardContinuous (Type u) (topology X) (smallEtaleTopology X) ⊣
      extend X :=
  (inclusion X).sheafAdjunctionCocontinuous (Type u) (topology X) (smallEtaleTopology X)

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts
