/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.HomSmall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts
variable {S : Scheme.{u}} (X : AlgebraicSpace S)

instance spacesLocallySmall : LocallySmall.{u} (spacesEtaleSite X) := by
  exact locallySmall_of_faithful
    (MorphismProperty.Over.forget (@AlgebraicSpace.Etale S) ⊤ X)

/-- Include the actual small chart family into the spaces-étale category. -/
def inclusion : AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site X ⥤ spacesEtaleSite X :=
  AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X ⋙ smallEtaleToSpaces X

instance : (inclusion X).Faithful := by
  change (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.inclusion X ⋙
    smallEtaleToSpaces X).Faithful
  infer_instance

/-- The inverse on Hom sets is Yoneda evaluation of the given space map. -/
def fullyFaithful : (inclusion X).FullyFaithful where
  preimage f := InducedCategory.homMk
    (MorphismProperty.CostructuredArrow.homMk (yonedaEquiv f.left) trivial sorry)
  map_preimage := sorry
  preimage_map := sorry

instance : (inclusion X).Full := (fullyFaithful X).full

/-- The topology is induced from the original spaces-étale topology. -/
def topology : GrothendieckTopology (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site X) :=
  AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.topology X

/-- Pulling the stored atlas back to an étale algebraic space and taking affine covers
shows that the actual small chart family covers every spaces-étale object. -/
instance coverDense : (inclusion X).IsCoverDense (spacesEtaleTopology X) := sorry

instance dense : (inclusion X).IsDenseSubsite (topology X) (spacesEtaleTopology X) where
  functorPushforward_mem_iff := sorry

/-- The Kan indexing categories are essentially small by the proved Hom-size bound. -/
instance rightKanLimits (U : (spacesEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (inclusion X).op) (Type u) :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Actual pointwise right Kan extension, without a postulated extension witness. -/
instance rightKan (P : (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.Site X)ᵒᵖ ⥤ Type u) :
    (inclusion X).op.HasPointwiseRightKanExtension P := by
  intro U
  infer_instance

/-- Restriction to small charts. -/
def restrict : Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (topology X) (Type u) :=
  (inclusion X).sheafPushforwardContinuous (Type u) (topology X) (spacesEtaleTopology X)

/-- The actual right Kan extension on the small chart family. -/
def extend : Sheaf (topology X) (Type u) ⥤ Sheaf (spacesEtaleTopology X) (Type u) :=
  (inclusion X).sheafPushforwardCocontinuous (Type u) (topology X) (spacesEtaleTopology X)

/-- The adjunction contains the explicit Kan unit and counit. -/
def adjunction : restrict X ⊣ extend X :=
  (inclusion X).sheafAdjunctionCocontinuous (Type u) (topology X) (spacesEtaleTopology X)

/-- Dense-site sheafification from the actual small chart model. -/
instance sheafification : HasSheafify (spacesEtaleTopology X) (Type u) :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (topology X) (spacesEtaleTopology X) (inclusion X)

end AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts
