module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-! # Reduced atlas and sheaf image of a closed subset

The vanishing ideal of the inverse image of a closed subset on an étale atlas defines a
reduced closed subscheme. Its relative sheaf image is a subfunctor of the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.AtlasImage

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))

/-- The scheme of the ambient algebraic space's étale atlas, over the base. -/
abbrev atlasScheme := AtlasInput.scheme X
/-- The morphism from the ambient étale atlas to the algebraic space. -/
abbrev atlasMap := AtlasInput.map X

/-- The actual inverse image of the specified closed set on the input atlas. -/
def closedOnAtlas : Closeds (atlasScheme X).left :=
  ⟨Points.mapOfOver (atlasMap X) ⁻¹' (Z : Set (Points X)),
    Z.isClosed.preimage (Points.continuous_mapOfOver (atlasMap X)
      (AtlasInput.representableEtale X))⟩

/-- The radical vanishing ideal of the closed subset on the atlas. -/
def ideal : (atlasScheme X).left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (closedOnAtlas X Z)

/-- The closed subscheme cut out by the vanishing ideal, regarded as a scheme over the base. -/
def reducedAtlas : Over S :=
  Over.mk ((ideal X Z).subschemeι ≫ (atlasScheme X).hom)

/-- The closed immersion of the reduced atlas into the ambient atlas. -/
def atlasInclusion : reducedAtlas X Z ⟶ atlasScheme X :=
  Over.homMk (ideal X Z).subschemeι rfl

/-- The image of the displayed inclusion is exactly the specified closed inverse image. -/
theorem atlasInclusion_range :
    Set.range (atlasInclusion X Z).left = (closedOnAtlas X Z : Set (atlasScheme X).left) := by
  change Set.range (ideal X Z).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The morphism from the reduced atlas to the ambient algebraic space. -/
def chartMap : yoneda.obj (reducedAtlas X Z) ⟶ X.functorOfPoints :=
  yoneda.map (atlasInclusion X Z) ≫ atlasMap X

/-- The fppf sheaf represented by the ambient algebraic space. -/
def ambientSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨X.functorOfPoints, X.isSheaf⟩

/-- The fppf sheaf represented by the reduced atlas. -/
def chartSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨yoneda.obj (reducedAtlas X Z), ofOver_isSheaf (reducedAtlas X Z)⟩

/-- The morphism of fppf sheaves induced by the reduced atlas map. -/
def chartSheafMap : chartSheaf X Z ⟶ ambientSheaf X :=
  ObjectProperty.homMk (chartMap X Z)

/-- The relative sheaf image of the reduced atlas inside the ambient algebraic space. -/
def imageSheaf : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  Sheaf.image (chartSheafMap X Z)

/-- The specified chart-to-image map comes from the relative image factorization. -/
def toImage : chartSheaf X Z ⟶ imageSheaf X Z :=
  Sheaf.toImage (chartSheafMap X Z)

/-- The image inclusion is literally the subtype-value map on sections. -/
def inclusion : imageSheaf X Z ⟶ ambientSheaf X :=
  Sheaf.imageι (chartSheafMap X Z)

/-- The reduced atlas map factors through its relative sheaf image. -/
theorem factorization : toImage X Z ≫ inclusion X Z = chartSheafMap X Z :=
  Sheaf.toImage_ι (chartSheafMap X Z)

/-- The inclusion of the relative sheaf image is a monomorphism. -/
instance inclusion_mono : Mono (inclusion X Z) := by
  change Mono (Sheaf.imageι (chartSheafMap X Z))
  infer_instance

/-- The map from the reduced atlas sheaf onto its image is an epimorphism. -/
instance toImage_epi : Epi (toImage X Z) := by
  change Epi (Sheaf.toImage (chartSheafMap X Z))
  infer_instance

/-- The relative image of the reduced atlas is an fppf sheaf. -/
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

