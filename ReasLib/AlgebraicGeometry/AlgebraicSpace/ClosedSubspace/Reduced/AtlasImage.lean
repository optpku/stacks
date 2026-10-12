/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-! # Actual reduced atlas and sheaf image for a closed subset of an algebraic space

Start with the existing input atlas, take the explicit scheme cut out by
the vanishing ideal of the inverse image of Z, and take its relative sheaf
image inside X. This constructs actual Type-u sheaf data without choosing
a closed subspace from the admitted exists_reduced theorem.

The remaining geometric step is to identify the atlas pullback of this
image with that explicit reduced closed subscheme. No algebraic-space
representability witness is selected or invented in this module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasImage

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))

abbrev atlasScheme := AtlasInput.scheme X
abbrev atlasMap := AtlasInput.map X

/-- The actual inverse image of the specified closed set on the input atlas. -/
def closedOnAtlas : Closeds (atlasScheme X).left :=
  ⟨Points.mapOfOver (atlasMap X) ⁻¹' (Z : Set (Points X)),
    Z.isClosed.preimage (Points.continuous_mapOfOver (atlasMap X)
      (AtlasInput.representableEtale X))⟩

/-- Mathlib's explicit radical vanishing ideal, not a selected ideal witness. -/
def ideal : (atlasScheme X).left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (closedOnAtlas X Z)

/-- The actual scheme quotient/gluing by that ideal, over the original base S. -/
def reducedAtlas : Over S :=
  Over.mk ((ideal X Z).subschemeι ≫ (atlasScheme X).hom)

/-- Its actual closed immersion into the original atlas scheme. -/
def atlasInclusion : reducedAtlas X Z ⟶ atlasScheme X :=
  Over.homMk (ideal X Z).subschemeι rfl

/-- The image of the displayed inclusion is exactly the specified closed inverse image. -/
theorem atlasInclusion_range :
    Set.range (atlasInclusion X Z).left = (closedOnAtlas X Z : Set (atlasScheme X).left) := by
  change Set.range (ideal X Z).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The actual map of the reduced atlas into X. -/
def chartMap : yoneda.obj (reducedAtlas X Z) ⟶ X.functorOfPoints :=
  yoneda.map (atlasInclusion X Z) ≫ atlasMap X

/-- The fppf sheaf of the original X, with its given sheaf law. -/
def ambientSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨X.functorOfPoints, X.isSheaf⟩

/-- The represented source sheaf uses the actual displayed scheme. -/
def chartSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨yoneda.obj (reducedAtlas X Z), ofOver_isSheaf (reducedAtlas X Z)⟩

def chartSheafMap : chartSheaf X Z ⟶ ambientSheaf X :=
  ObjectProperty.homMk (chartMap X Z)

/-- Relative sheaf image is a predicate/subtype of the original X(T),
computed by covering sieves. It requires no general big-site Type-u
sheafification existence certificate. -/
def imageSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  Sheaf.image (chartSheafMap X Z)

/-- The specified chart-to-image map comes from the relative image factorization. -/
def toImage : chartSheaf X Z ⟶ imageSheaf X Z :=
  Sheaf.toImage (chartSheafMap X Z)

/-- The image inclusion is literally the subtype-value map on sections. -/
def inclusion : imageSheaf X Z ⟶ ambientSheaf X :=
  Sheaf.imageι (chartSheafMap X Z)

theorem factorization : toImage X Z ≫ inclusion X Z = chartSheafMap X Z :=
  Sheaf.toImage_ι (chartSheafMap X Z)

instance inclusion_mono : Mono (inclusion X Z) := by
  change Mono (Sheaf.imageι (chartSheafMap X Z))
  infer_instance

instance toImage_epi : Epi (toImage X Z) := by
  change Epi (Sheaf.toImage (chartSheafMap X Z))
  infer_instance

/-- Sheafness is supplied by Mathlib's proved relative-image construction. -/
theorem image_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (imageSheaf X Z).obj :=
  (imageSheaf X Z).property

/-- On a chart point, the inclusion after factorization is the original
actual scheme inclusion followed by the supplied atlas map. -/
theorem inclusion_toImage_apply (T : Over S) (g : T ⟶ reducedAtlas X Z) :
    (inclusion X Z).hom.app (op T) ((toImage X Z).hom.app (op T) g) =
      (atlasMap X).app (op T) (g ≫ atlasInclusion X Z) := by
  exact ConcreteCategory.congr_hom (congr_app (congrArg (fun h ↦ h.hom)
    (factorization X Z)) (op T)) g

end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasImage

