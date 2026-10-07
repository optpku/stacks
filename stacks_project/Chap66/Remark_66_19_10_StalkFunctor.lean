module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_19_7_Point

/-!
# Identity geometric points and pullback-then-sections

The identity geometric point of `Spec k` associated to a geometric point `xbar` of an
algebraic space, and the functor sending a small étale sheaf to inverse image along
`xbar.hom` followed by the sheaf fibre at that identity point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)

/-- The identity geometric point of `Spec k` for the source field of `xbar`. -/
def idGeometricPoint : GeometricPoint (ofOver xbar.overObj) :=
  @of S (ofOver xbar.overObj) xbar.K inferInstance xbar.isAlgClosed xbar.structureHom
    (𝟙 (ofOver xbar.overObj))

/-- The source field of `idGeometricPoint xbar` is the source field of `xbar`. -/
@[simp]
theorem idGeometricPoint_K : (idGeometricPoint xbar).K = xbar.K :=
  sorry

/-- The structure morphism of `idGeometricPoint xbar` is the structure morphism of `xbar`. -/
@[simp]
theorem idGeometricPoint_structureHom :
    (idGeometricPoint xbar).structureHom = xbar.structureHom :=
  sorry

/-- The morphism of `idGeometricPoint xbar` is the identity of `Spec k`. -/
@[simp]
theorem idGeometricPoint_hom :
    (idGeometricPoint xbar).hom = 𝟙 (ofOver xbar.overObj) :=
  sorry

/-- Postcomposition of the identity geometric point of `Spec k` along `xbar.hom` recovers
the morphism of `xbar`. -/
theorem idGeometricPoint_map_hom :
    ((idGeometricPoint xbar).map xbar.hom).hom = xbar.hom :=
  sorry

/-- The image in `|X|` of the postcomposed identity geometric point agrees with the image of
`xbar`. -/
theorem idGeometricPoint_map_image :
    ((idGeometricPoint xbar).map xbar.hom).image = xbar.image :=
  sorry

variable [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
    (etaleBaseChange xbar.hom).op.HasLeftKanExtension F]

/-- Pullback along `xbar` followed by the sheaf fibre at the identity geometric point of
`Spec k`. -/
def pullbackThenSections :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafInverseImage (Type (u + 1)) xbar.hom ⋙
    (toSmallEtalePoint (idGeometricPoint xbar)).sheafFiber

/-- The pullback-then-sections functor evaluates by inverse image then identity-point fibre. -/
theorem pullbackThenSections_obj (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (pullbackThenSections xbar).obj F =
      (toSmallEtalePoint (idGeometricPoint xbar)).sheafFiber.obj
        ((sheafInverseImage (Type (u + 1)) xbar.hom).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
